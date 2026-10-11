#include "CheckedCandidate.h"
#include "ComputationSelection.h"
#include "LaneRealization.h"
#include "MathematicalComparison.h"
#include "MathematicalSupport.h"
#include "RealizationEmission.h"
#include "RealizationTrace.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include <optional>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
// Shape checks compare every rowwise input with the first one, including
// inputs the formula never reads, before any arithmetic. They use the
// installed ordered control.require: a mismatch is a local backend stop of
// this checked operation, as for polynomial realization shape checks.
constexpr StringLiteral shapeGuard = "control.require";

bool boundWithoutField(StringRef contract) {
  return contract.starts_with("index.") || contract == shapeGuard;
}

// Expand one map's helper into a detached scalar function. Its single block is
// the complete scalar formula; the Ring view admits every operation in it,
// including unused ones, and preserves every input slot. The helper and its
// callees are cloned, never edited. The root helper is charged to the shared
// budgets before it is cloned, as helper observation does; inlining then
// charges only the callees it expands.
FailureOr<OwningOpRef<func::FuncOp>>
scalarFormula(algebra::MapRealizeOp map, protocol_ir::ProtocolModuleOp unit,
              SymbolTableCollection &symbols, unsigned &remaining,
              uint64_t &indices, uint64_t *work = nullptr,
              OptimizationOutcome *outcome = nullptr) {
  auto helper = symbols.lookupSymbolIn<func::FuncOp>(unit, map.getHelperAttr());
  if (!helper || helper.isExternal() || !helper.getBody().hasOneBlock()) {
    diagnostics::emit(map.emitOpError(), "algebra-map-helper",
                      "expected a helper body");
    return failure();
  }
  if (failed(chargeHelperOperations(helper, remaining, indices, work, outcome)))
    return failure();
  OwningOpRef<func::FuncOp> scratch(cast<func::FuncOp>(helper->clone()));
  if (failed(inlineHelpers(*scratch, remaining, indices, symbols, unit, work,
                           outcome)))
    return failure();
  auto &body = scratch->front();
  if (body.getNumArguments() != map.getRowwise().size() ||
      body.back().getNumOperands() != 1) {
    diagnostics::emit(map.emitOpError(), "algebra-map-signature",
                      "helper ports differ from the mapped signature");
    return failure();
  }
  auto expression =
      algebra::describeRingExpression(body, body.back().getOperands());
  if (!expression) {
    diagnostics::emit(map.emitOpError(), "algebra-map-formula",
                      toString(expression.takeError()));
    return failure();
  }
  return std::move(scratch);
}

// Lower a checked map with O(formula) operations, independent of the runtime
// row count. Scalar subexpressions stay scalar. A scalar meets rows through
// vector.scale for multiplication; for addition and subtraction its broadcast
// vector.fill(scalar, rows) is emitted immediately before the first operation
// that needs it and reused afterwards. A scalar result is broadcast likewise.
class MapRealizer {
  OpBuilder builder;
  RealizationEmitter emitter;
  unsigned nextSite = 0;
  Location loc;
  algebra::FieldType field;
  Type index, boolean, vector;
  Value rows;

  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> parameters = {}) {
    std::vector<std::string> arguments;
    if (!boundWithoutField(contract))
      arguments.push_back(field.getDomain().str());
    SmallVector<Type> outputs;
    if (output)
      outputs.push_back(output);
    auto *op = emitter.emit(builder, loc, "map_" + std::to_string(nextSite++),
                            {contract.str(), std::move(arguments), ""}, inputs,
                            outputs, parameters);
    return output ? op->getResult(0) : Value();
  }

public:
  explicit MapRealizer(protocol_ir::ProtocolModuleOp unit)
      : builder(unit.getContext()), emitter(unit, "_map_binding_"),
        loc(unit.getLoc()) {}
  LogicalResult run(algebra::MapRealizeOp map, Block &formula,
                    RealizationScope &scope) {
    loc = map.getLoc();
    nextSite = 0;
    auto signature = map.getFunctionType();
    field = cast<algebra::FieldType>(
        algebra::mapField(signature, map.getRowwise()));
    vector = signature.getResult(0);
    index = IntegerType::get(builder.getContext(), 64, IntegerType::Unsigned);
    boolean = builder.getI1Type();
    builder.setInsertionPointAfter(map);
    auto function =
        local::FuncOp::create(builder, loc, map.getSymName(), signature);
    function->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr(map.getHelper()),
                              builder.getArrayAttr({})}));
    auto *entry = function.addEntryBlock();
    builder.setInsertionPointToEnd(entry);
    auto rowwise = map.getRowwise();
    rows = Value();
    for (auto [i, mapped] : llvm::enumerate(rowwise)) {
      if (!mapped)
        continue;
      Value length = emit("vector.length", entry->getArgument(i), index);
      if (!rows)
        rows = length;
      else
        emit(shapeGuard, emit("index.equal", {rows, length}, boolean), Type());
    }
    const auto &recipes = mathematicalRecipes();
    OptimizationOutcome outcome;
    auto selection = selectLaneFormula(formula, rowwise, recipes, &outcome);
    scope.selection(map, DecisionFamily::Map, RealizationChoice::Elementwise,
                    outcome);
    if (!selection)
      return diagnostics::emit(map.emitOpError(),
                               "mathematical-lane-unsupported",
                               "required map has no supported lane formula");
    llvm::DenseMap<Value, LaneInput> values;
    for (auto [i, argument] : llvm::enumerate(formula.getArguments()))
      values[argument] = {entry->getArgument(i), rowwise[i]};
    // Required maps have already charged their complete expanded helpers to
    // the stage's operation/slot budgets. The optional finite-selection budget
    // must not introduce a stricter second admission limit here.
    auto result =
        realizeLanes(formula, values, vector, rows, nullptr, recipes,
                     [&](StringRef contract, ValueRange operands, Type output,
                         ArrayRef<std::string> parameters) {
                       return emit(contract, operands, output, parameters);
                     });
    if (!result)
      return diagnostics::emit(map.emitOpError(), result.takeError());
    if (result->status != LaneRealizationStatus::Realized) {
      scope.selection(map, DecisionFamily::Lanes,
                      RealizationChoice::Elementwise, result->outcome);
      scope.failure(RequiredFailure{"required map realization is unavailable",
                                    result->outcome.capacity});
      return diagnostics::emit(map.emitOpError(), result->reason,
                               "required map realization is unavailable");
    }
    local::ReturnOp::create(builder, loc, result->value);
    map.erase();
    return success();
  }
};

// Check ordered input admission, then independently compare the actual
// candidate payload with the retained source formula.
class MapCorrespondence {
  SymbolTable &symbols;
  llvm::DenseSet<Operation *> &bindings;
  uint64_t &remaining;
  StringRef domain;
  Type field, vector, index, boolean;
  Operation *cursor = nullptr;
  bool valid = true;
  unsigned nextSite = 0;
  Value rows;

  Value primitive(StringRef contract, ValueRange operands, Type output,
                  ArrayRef<std::string> parameters = {}) {
    if (!valid || !remaining || !cursor) {
      valid = false;
      return {};
    }
    --remaining;
    Operation *op = cursor;
    cursor = cursor->getNextNode();
    auto site = op->getAttrOfType<StringAttr>("site");
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto declaration =
        ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
            : local::OperationBindingOp();
    SmallVector<std::string> arguments;
    if (!boundWithoutField(contract))
      arguments.push_back(domain.str());
    auto strings = [](ArrayAttr attrs, ArrayRef<std::string> expected) {
      return attrs && attrs.size() == expected.size() &&
             all_of(zip(attrs, expected), [](auto pair) {
               auto text = dyn_cast<StringAttr>(std::get<0>(pair));
               return text && text.getValue() == std::get<1>(pair);
             });
    };
    if (op->getName().getStringRef() !=
            protocol::boundOperationName(contract) ||
        !site || site.getValue() != "map_" + std::to_string(nextSite++) ||
        !declaration || declaration.getContract() != contract ||
        !declaration.getImplementation().empty() ||
        !strings(declaration.getArguments(), arguments) ||
        !strings(op->getAttrOfType<ArrayAttr>("parameters"), parameters) ||
        op->getAttrs().size() != 3 || op->getNumRegions() ||
        op->getNumResults() != unsigned(bool(output)) ||
        (output && op->getResult(0).getType() != output) ||
        !llvm::equal(op->getOperands(), operands)) {
      valid = false;
      return {};
    }
    bindings.insert(declaration);
    return output ? op->getResult(0) : Value();
  }

public:
  MapCorrespondence(SymbolTable &symbols, llvm::DenseSet<Operation *> &bindings,
                    uint64_t &remaining)
      : symbols(symbols), bindings(bindings), remaining(remaining) {}
  LogicalResult check(algebra::MapRealizeOp source, local::FuncOp function,
                      Block &formula) {
    auto *context = source.getContext();
    auto signature = source.getFunctionType();
    auto scalar = dyn_cast_if_present<algebra::FieldType>(
        algebra::mapField(signature, source.getRowwise()));
    auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
    if (!scalar || function.getSymName() != source.getSymName() ||
        function.getFunctionType() != signature ||
        function->getAttrs().size() != 3 || !origin || origin.size() != 2 ||
        origin[0] != StringAttr::get(context, source.getHelper()) ||
        origin[1] != ArrayAttr::get(context, {}) ||
        !function.getBody().hasOneBlock() ||
        formula.getNumArguments() != signature.getNumInputs())
      return failure();
    domain = scalar.getDomain();
    field = scalar;
    vector = signature.getResult(0);
    index = IntegerType::get(context, 64, IntegerType::Unsigned);
    boolean = IntegerType::get(context, 1);
    auto &entry = function.getBody().front();
    cursor = &entry.front();
    auto rowwise = source.getRowwise();
    // Every rowwise input, used or not, is measured and compared with the
    // first before any formula operation.
    for (auto [i, mapped] : llvm::enumerate(rowwise)) {
      if (!mapped)
        continue;
      Value length = primitive("vector.length", entry.getArgument(i), index);
      if (!rows)
        rows = length;
      else
        primitive(shapeGuard, primitive("index.equal", {rows, length}, boolean),
                  Type());
    }
    if (!rows)
      return failure();
    auto result =
        compareLaneFormula(formula, rowwise, entry.getArguments(), rows, cursor,
                           symbols, bindings, remaining, &entry.back());
    if (failed(result) || !valid || !cursor || !isa<local::ReturnOp>(cursor) ||
        cursor->getNextNode() || !cursor->getAttrs().empty() ||
        !llvm::equal(cursor->getOperands(), ValueRange{*result}))
      return failure();
    return success();
  }
};

FailureOr<protocol_ir::ProtocolModuleOp> protocolUnit(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return failure();
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return failure();
  return unit;
}
} // namespace

LogicalResult verifyMapRealizationsPreserved(ModuleOp original,
                                             ModuleOp candidate) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  auto refuse = [&](StringRef reason) {
    return diagnostics::emit(candidate.emitError(),
                             "algebra-map-correspondence", reason);
  };
  auto before = protocolUnit(original);
  auto after = protocolUnit(candidate);
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      failed(before) || failed(after) ||
      (*before)->getAttrDictionary() != (*after)->getAttrDictionary())
    return refuse("module shape or profile");
  SymbolTable symbols(*after);
  SymbolTable originalSymbols(*before);
  llvm::DenseSet<Operation *> retained, bindings;
  uint64_t remaining = 1000000;
  for (Operation &op : before->getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    if (!name)
      return refuse("unnamed declaration");
    Operation *replacement = symbols.lookup(name.getValue());
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    if (auto map = dyn_cast<algebra::MapRealizeOp>(op)) {
      // Interpret the original helper closure directly. Sharing the producer's
      // inlined scratch body would also share capture-substitution mistakes.
      auto function = dyn_cast<local::FuncOp>(replacement);
      auto helper = originalSymbols.lookup<func::FuncOp>(map.getHelper());
      if (!function || !helper || !helper.getBody().hasOneBlock())
        return refuse("realization declaration or formula");
      if (failed(MapCorrespondence(symbols, bindings, remaining)
                     .check(map, function, helper.getBody().front())))
        return refuse(remaining ? "realization body" : "work limit");
    } else if (!OperationEquivalence::isEquivalentTo(
                   &op, replacement, OperationEquivalence::IgnoreLocations))
      return refuse("changed retained declaration");
  }
  for (auto &op : (*after).getBody().front())
    if (!retained.contains(&op) && !bindings.contains(&op))
      return refuse("unexpected declaration");
  return success();
}

LogicalResult expandMapRealizations(ModuleOp module, RealizationWork *work,
                                    RealizationTrace *trace) {
  RealizationWork standalone;
  auto &stageWork = work ? *work : standalone;
  RealizationScope scope(trace, "map-realizations", module, {}, &stageWork);
  if (failed(verify(module)))
    return failure();
  auto original = protocolUnit(module);
  if (failed(original))
    return diagnostics::emit(module.emitError(), "algebra-map-context",
                             "expected the 'protocol' profile");
  if (original->getBody().front().getOps<algebra::MapRealizeOp>().empty()) {
    scope.complete(CompletionKind::Unchanged);
    return success();
  }
  scope.propose();
  mathematical::CheckedCandidate candidate(module);
  auto unit = *protocolUnit(*candidate);
  // Derive every formula before editing the candidate's symbol table.
  SmallVector<std::pair<algebra::MapRealizeOp, OwningOpRef<func::FuncOp>>> maps;
  {
    SymbolTableCollection symbols;
    auto &helpers = stageWork.helperOperations;
    auto &indices = stageWork.helperSlots;
    for (auto map : unit.getBody().front().getOps<algebra::MapRealizeOp>()) {
      OptimizationOutcome outcome;
      auto formula = scalarFormula(map, unit, symbols, helpers, indices,
                                   nullptr, &outcome);
      if (failed(formula)) {
        scope.failure(
            RequiredFailure{"required map helper expansion", outcome.capacity});
        return failure();
      }
      maps.emplace_back(map, std::move(*formula));
    }
  }
  MapRealizer realizer(unit);
  for (auto &[map, formula] : maps)
    if (failed(realizer.run(map, formula->front(), scope)))
      return failure();
  scope.failure(VerificationDecision{
      VerificationObservation::Refused, "required map correspondence", {}, {}});
  if (failed(candidate.publish(verifyMapRealizationsPreserved)))
    return diagnostics::emit(module.emitError(), "algebra-map-lowering",
                             "realized map failed its correspondence check");
  scope.publish();
  return success();
}

FailureOr<std::map<std::string, std::pair<unsigned, unsigned>>>
describeMapProducts(ModuleOp module, RealizationTrace *trace) {
  RealizationScope scope(trace, "map-products", module);
  auto unit = protocolUnit(module);
  if (failed(unit))
    return failure();
  std::map<std::string, std::pair<unsigned, unsigned>> products;
  SymbolTableCollection symbols;
  unsigned helpers = realizedHelperOperationLimit;
  uint64_t indices = 1000000;
  for (auto map : unit->getBody().front().getOps<algebra::MapRealizeOp>()) {
    OptimizationOutcome expansionOutcome;
    auto formula = scalarFormula(map, *unit, symbols, helpers, indices, nullptr,
                                 &expansionOutcome);
    if (failed(formula)) {
      scope.failure(
          RequiredFailure{"map formula admission", expansionOutcome.capacity});
      return failure();
    }
    auto &body = (*formula)->front();
    OptimizationOutcome outcome;
    auto product = selectMapProduct(body, map.getRowwise(), &outcome);
    scope.selection(map, DecisionFamily::MapProduct,
                    product ? RealizationChoice::MapProduct
                            : RealizationChoice::Ordered,
                    outcome);
    if (product)
      products.emplace(map.getSymName().str(), *product);
  }
  scope.complete();
  return products;
}

FailureOr<Value> compareMapSum(algebra::MapRealizeOp map, ValueRange inputs,
                               Value rows, Operation *&cursor,
                               SymbolTable &candidateSymbols,
                               llvm::DenseSet<Operation *> &bindings,
                               uint64_t &remaining) {
  auto unit = map->getParentOfType<protocol_ir::ProtocolModuleOp>();
  auto helper =
      unit ? dyn_cast_or_null<func::FuncOp>(
                 SymbolTable::lookupSymbolIn(unit, map.getHelperAttr()))
           : func::FuncOp();
  if (!helper || !helper.getBody().hasOneBlock())
    return failure();
  return compareLaneSum(helper.getBody().front(), map.getRowwise(), inputs,
                        rows, cursor, candidateSymbols, bindings, remaining);
}

Error checkMapFormulas(ModuleOp original, uint64_t &remaining) {
  auto unit = protocolUnit(original);
  if (failed(unit))
    return error("target.admission", "expected mathematical protocol profile");
  if (unit->getBody().front().getOps<algebra::MapRealizeOp>().empty())
    return Error::success();
  std::optional<diagnostics::RefusalInfo> refusal;
  // Record the first identified refusal and let enclosing handlers keep the
  // located diagnostic.
  ScopedDiagnosticHandler handler(original.getContext(), [&](Diagnostic &d) {
    if (!refusal)
      if (auto found = diagnostics::refusals(d); !found.empty())
        refusal = found.front();
    return failure();
  });
  SymbolTableCollection symbols;
  unsigned helpers =
      std::min<uint64_t>(realizedHelperOperationLimit, remaining);
  uint64_t indices = std::min<uint64_t>(1000000, remaining);
  for (auto map : unit->getBody().front().getOps<algebra::MapRealizeOp>()) {
    if (!remaining)
      return error("source.limit", "map formula admission work exhausted");
    --remaining;
    if (failed(
            scalarFormula(map, *unit, symbols, helpers, indices, &remaining)))
      return refusal ? error(refusal->code, refusal->detail)
                     : error("algebra-map-formula", "formula refused");
  }
  return Error::success();
}
} // namespace zkc::mathematical
