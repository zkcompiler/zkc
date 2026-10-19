#include "CheckedCandidate.h"
#include "ComputationSelection.h"
#include "LaneRealization.h"
#include "MapOccurrence.h"
#include "MathematicalComparison.h"
#include "MathematicalSupport.h"
#include "RealizationEmission.h"
#include "RealizationTrace.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Numerical.h"
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
constexpr uint64_t mapComparisonWorkLimit = 1000000;

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

public:
  explicit MapRealizer(protocol_ir::ProtocolModuleOp unit)
      : builder(unit.getContext()), emitter(unit, "_map_binding_") {}
  LogicalResult run(algebra::MapRealizeOp map, Block &formula,
                    RealizationScope &scope, NumericalExpressionMode mode,
                    local::FuncOp *numerical = nullptr) {
    if (numerical)
      *numerical = {};
    builder.setInsertionPointAfter(map);
    auto function = local::FuncOp::create(
        builder, map.getLoc(), map.getSymName(), map.getFunctionType());
    function->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr(map.getHelper()),
                              builder.getArrayAttr({})}));
    auto *entry = function.addEntryBlock();
    unsigned nextSite = 0;
    auto emit = [&](const protocol::BindingApplication &application,
                    ValueRange operands, TypeRange outputs,
                    ArrayRef<std::string> parameters) {
      return emitter.emit(builder, map.getLoc(),
                          "map_" + std::to_string(nextSite++), application,
                          operands, outputs, parameters);
    };
    builder.setInsertionPointToEnd(entry);
    auto result = emitMapPayload(map, formula, entry->getArguments(),
                                 mode == NumericalExpressionMode::PreferNative
                                     ? MapPayloadForm::NumericalMap
                                     : MapPayloadForm::VectorMap,
                                 emit);
    if (!result)
      return diagnostics::emit(map.emitOpError(), result.takeError());
    if (mode == NumericalExpressionMode::PreferNative &&
        result->status != LaneRealizationStatus::Realized) {
      scope.selection(map, DecisionFamily::Lanes,
                      RealizationChoice::Elementwise, result->outcome);
      // The native payload capacity gate emits no payload. Remove its ordered
      // guard prefix before invoking the same worker for the required form.
      while (!entry->empty())
        entry->back().erase();
      nextSite = 0;
      builder.setInsertionPointToEnd(entry);
      result = emitMapPayload(map, formula, entry->getArguments(),
                              MapPayloadForm::VectorMap, emit);
    } else if (mode == NumericalExpressionMode::PreferNative && numerical)
      *numerical = function;
    if (!result)
      return diagnostics::emit(map.emitOpError(), result.takeError());
    if (result->status != LaneRealizationStatus::Realized)
      return diagnostics::emit(map.emitOpError(), result->reason,
                               "required map realization is unavailable");
    scope.selection(map, DecisionFamily::Map, RealizationChoice::Elementwise,
                    OptimizationOutcome::success());
    local::ReturnOp::create(builder, map.getLoc(), result->value);
    map.erase();
    return success();
  }
};

// Strict declaration wrapper around the same independent occurrence reader.
class MapCorrespondence {
  SymbolTable &symbols;
  llvm::DenseSet<Operation *> &bindings;
  uint64_t &remaining;
  ComparisonCapacity capacity = ComparisonCapacity::None;

public:
  MapCorrespondence(SymbolTable &symbols, llvm::DenseSet<Operation *> &bindings,
                    uint64_t &remaining)
      : symbols(symbols), bindings(bindings), remaining(remaining) {}
  ComparisonCapacity exhausted() const { return capacity; }
  LogicalResult check(algebra::MapRealizeOp source, local::FuncOp function,
                      Block &formula, uint64_t *numericalRemaining = nullptr) {
    auto *context = source.getContext();
    auto signature = source.getFunctionType();
    auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
    if (function.getSymName() != source.getSymName() ||
        function.getFunctionType() != signature ||
        function->getAttrs().size() != 3 || !origin || origin.size() != 2 ||
        origin[0] != StringAttr::get(context, source.getHelper()) ||
        origin[1] != ArrayAttr::get(context, {}) ||
        !function.getBody().hasOneBlock() ||
        formula.getNumArguments() != signature.getNumInputs())
      return failure();
    auto &entry = function.getBody().front();
    if (entry.empty() || !isa<local::ReturnOp>(entry.back()) ||
        !entry.back().getAttrs().empty() || entry.back().getNumOperands() != 1)
      return failure();
    unsigned nextSite = 0;
    for (auto &op : entry.without_terminator()) {
      auto site = op.getAttrOfType<StringAttr>("site");
      if (!site || site.getValue() != "map_" + std::to_string(nextSite++))
        return failure();
    }
    auto *cursor = &entry.front();
    VerificationDecision outcome;
    auto result = readMapPayload(
        source, entry.getArguments(), false, cursor, &entry.back(),
        entry.back().getOperand(0), symbols, bindings, remaining,
        numericalRemaining ? *numericalRemaining : remaining, outcome);
    if (outcome.outcome == VerificationObservation::OptionalCapacity ||
        outcome.outcome == VerificationObservation::RequiredCapacity)
      capacity = ComparisonCapacity::Work;
    return success(succeeded(result) && cursor == &entry.back() &&
                   *result == entry.back().getOperand(0));
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

FailureOr<OwningOpRef<func::FuncOp>>
prepareMapFormula(algebra::MapRealizeOp map, RealizationWork &work) {
  auto unit = map->getParentOfType<protocol_ir::ProtocolModuleOp>();
  SymbolTableCollection symbols;
  return scalarFormula(map, unit, symbols, work.helperOperations,
                       work.helperSlots);
}

Expected<LaneRealizationResult>
emitMapPayload(algebra::MapRealizeOp map, Block &formula, ValueRange inputs,
               MapPayloadForm form, MapEmitter emit,
               const SelectedReduction *dot) {
  auto vector = map.getFunctionType().getResult(0);
  auto field = cast<algebra::FieldType>(
      algebra::mapField(map.getFunctionType(), map.getRowwise()));
  auto primitive = [&](StringRef contract, ValueRange operands, Type output,
                       ArrayRef<std::string> parameters = {}) -> Operation * {
    std::vector<std::string> arguments;
    if (!boundWithoutField(contract))
      arguments.push_back(field.getDomain().str());
    SmallVector<Type> outputs;
    if (output)
      outputs.push_back(output);
    return emit({contract.str(), std::move(arguments), ""}, operands, outputs,
                parameters);
  };
  auto rowwise = map.getRowwise();
  if (inputs.size() != rowwise.size())
    return error("algebra-map-signature");
  Value rows;
  auto index = IntegerType::get(map.getContext(), 64, IntegerType::Unsigned);
  for (auto [i, mapped] : enumerate(rowwise)) {
    if (!mapped)
      continue;
    auto *length = primitive("vector.length", inputs[i], index);
    if (!length)
      return error("mathematical-lane-realization");
    if (!rows)
      rows = length->getResult(0);
    else {
      auto *equal = primitive("index.equal", {rows, length->getResult(0)},
                              IntegerType::get(map.getContext(), 1));
      if (!equal || !primitive(shapeGuard, equal->getResult(0), {}))
        return error("mathematical-lane-realization");
    }
  }
  const auto &recipes = mathematicalRecipes();
  if (form == MapPayloadForm::Dot) {
    std::optional<SelectedReduction> selected;
    if (!dot) {
      auto product = selectMapProduct(formula, rowwise);
      if (product)
        selected = selectMapSum(*product, recipes);
      if (selected)
        dot = &*selected;
    }
    if (!dot)
      return error("mathematical-lane-realization",
                   "missing admitted dot rule");
    SmallVector<Value> operands;
    for (auto i : dot->inputs)
      operands.push_back(inputs[i]);
    auto *op = primitive(dot->recipe->target, operands, field);
    if (!op)
      return error("mathematical-lane-realization");
    return LaneRealizationResult{
        LaneRealizationStatus::Realized, op->getResult(0), {}};
  }
  llvm::DenseMap<Value, LaneInput> values;
  for (auto [i, argument] : enumerate(formula.getArguments()))
    values[argument] = {inputs[i], rowwise[i]};
  // Complete helper admission was charged before preparation. Required maps
  // do not acquire a second optional recognition ceiling here.
  auto admitted = admitLaneFormula(formula, values, vector, nullptr, recipes);
  if (!admitted)
    return admitted.takeError();
  if (!admitted->formula)
    return LaneRealizationResult{
        admitted->status, {}, admitted->reason, admitted->outcome};
  if (form != MapPayloadForm::VectorMap)
    return emitNumericalLanes(
        *admitted->formula, vector, rows,
        form == MapPayloadForm::NumericalSum ? LaneResultMode::Sum
                                             : LaneResultMode::Map,
        [&](const protocol::BindingApplication &application,
            ValueRange operands, Type output,
            ArrayRef<std::string> parameters) {
          auto *op = emit(application, operands, TypeRange{output}, parameters);
          return op ? op->getResult(0) : Value();
        });
  return emitVectorLanes(*admitted->formula, vector, rows, recipes,
                         [&](StringRef contract, ValueRange operands,
                             Type output, ArrayRef<std::string> parameters) {
                           auto *op = primitive(contract, operands, output,
                                                parameters);
                           return op ? op->getResult(0) : Value();
                         });
}

FailureOr<Value> readMapPayload(algebra::MapRealizeOp source, ValueRange inputs,
                                bool sum, Operation *&cursor, Operation *end,
                                Value output, SymbolTable &symbols,
                                llvm::DenseSet<Operation *> &bindings,
                                uint64_t &requiredWork, uint64_t &optionalWork,
                                VerificationDecision &outcome) {
  outcome = {VerificationObservation::Mismatch, "map payload differs"};
  auto unit = source->getParentOfType<protocol_ir::ProtocolModuleOp>();
  auto helper = dyn_cast_or_null<func::FuncOp>(
      SymbolTable::lookupSymbolIn(unit, source.getHelperAttr()));
  if (!helper || !helper.getBody().hasOneBlock() ||
      inputs.size() != source.getRowwise().size())
    return failure();
  bool optional = sum;
  for (auto *at = cursor; at && at != end; at = at->getNextNode())
    if (auto ref = at->getAttrOfType<FlatSymbolRefAttr>("binding"))
      if (auto binding =
              symbols.lookup<local::OperationBindingOp>(ref.getValue()))
        optional |= protocol::numericalContract(binding.getContract());
  auto &remaining = optional ? optionalWork : requiredWork;
  auto exhaust = [&](std::optional<CapacityCause> debit = {}) {
    outcome = {optional ? VerificationObservation::OptionalCapacity
                        : VerificationObservation::RequiredCapacity,
               "map comparison capacity", debit};
  };
  Operation *at = cursor;
  llvm::DenseSet<Operation *> used;
  auto field = cast<algebra::FieldType>(
      algebra::mapField(source.getFunctionType(), source.getRowwise()));
  auto primitive = [&](StringRef contract, ValueRange operands,
                       Type result) -> Operation * {
    if (!at || at == end)
      return nullptr;
    if (!remaining) {
      exhaust(CapacityCause{optional ? WorkOwner::OptionalComparison
                                     : WorkOwner::AlgorithmChecking,
                            1, 0});
      return nullptr;
    }
    --remaining;
    auto ref = at->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
            : local::OperationBindingOp();
    SmallVector<Attribute> arguments;
    if (!boundWithoutField(contract))
      arguments.push_back(
          StringAttr::get(source.getContext(), field.getDomain()));
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding->getAttrs().size() != 4 ||
        binding.getArguments() !=
            ArrayAttr::get(source.getContext(), arguments) ||
        at->getName().getStringRef() !=
            protocol::boundOperationName(contract) ||
        !at->getAttrOfType<StringAttr>("site") || at->getAttrs().size() != 3 ||
        at->getAttrOfType<ArrayAttr>("parameters") !=
            ArrayAttr::get(source.getContext(), {}) ||
        at->getNumRegions() || at->getNumResults() != unsigned(bool(result)) ||
        (result && at->getResult(0).getType() != result) ||
        !llvm::equal(at->getOperands(), operands))
      return nullptr;
    used.insert(binding);
    auto *read = at;
    at = at->getNextNode();
    return read;
  };
  Value rows;
  auto index = IntegerType::get(source.getContext(), 64, IntegerType::Unsigned);
  for (auto [i, mapped] : enumerate(source.getRowwise())) {
    if (!mapped)
      continue;
    auto *length = primitive("vector.length", inputs[i], index);
    if (!length)
      return failure();
    if (!rows)
      rows = length->getResult(0);
    else {
      auto *equal = primitive("index.equal", {rows, length->getResult(0)},
                              IntegerType::get(source.getContext(), 1));
      if (!equal || !primitive(shapeGuard, equal->getResult(0), {}))
        return failure();
    }
  }
  ComparisonCapacity capacity = ComparisonCapacity::None;
  std::optional<CapacityCause> debit;
  // An identity map may return a mapped input without consuming its suffix.
  // The explicit span also admits unused payload operations after the result;
  // the enclosing reader checks the actual use of the returned SSA value.
  auto result =
      sum ? compareLaneSum(helper.getBody().front(), source.getRowwise(),
                           inputs, rows, at, symbols, used, remaining, end,
                           &capacity, &debit, output)
          : compareLaneFormula(helper.getBody().front(), source.getRowwise(),
                               inputs, rows, at, symbols, used, remaining, end,
                               &capacity, &debit, output);
  if (failed(result)) {
    if (capacity != ComparisonCapacity::None)
      exhaust(debit);
    return failure();
  }
  if (at != end)
    return failure();
  bindings.insert(used.begin(), used.end());
  cursor = at;
  outcome = {VerificationObservation::Verified, {}};
  return result;
}

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
  uint64_t remaining = mapComparisonWorkLimit;
  uint64_t numericalRemaining = mapComparisonWorkLimit;
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
      MapCorrespondence comparison(symbols, bindings, remaining);
      if (failed(comparison.check(map, function, helper.getBody().front(),
                                  &numericalRemaining)))
        return refuse(comparison.exhausted() == ComparisonCapacity::None
                          ? "realization body"
                          : "work limit");
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
                                    RealizationTrace *trace,
                                    NumericalExpressionMode mode) {
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
  SymbolTable originalSymbols(*original);
  struct NumericalMap {
    algebra::MapRealizeOp source;
    local::FuncOp function;
    Block *formula;
  };
  SmallVector<NumericalMap> numericalMaps, declined;
  for (auto &[map, formula] : maps) {
    auto sourceMap =
        originalSymbols.lookup<algebra::MapRealizeOp>(map.getSymName());
    local::FuncOp numerical;
    if (failed(realizer.run(map, formula->front(), scope, mode, &numerical)))
      return failure();
    if (numerical)
      numericalMaps.push_back({sourceMap, numerical, &formula->front()});
  }
  // Retained native comparisons fit the final reader's equal-sized optional
  // allowance; required checking has its own untouched reserve.
  uint64_t numericalRemaining = mapComparisonWorkLimit;
  llvm::DenseSet<Operation *> declinedBindings;
  {
    // Build the symbol inventory once, after emission. Checking many native
    // candidates must not repeatedly scan every declaration in the module.
    SymbolTable symbols(unit);
    for (auto proposal : numericalMaps) {
      // Interpret the immutable original helper closure. Spent optional work
      // is never restored; an unexamined candidate is discarded on exhaustion.
      auto helper =
          originalSymbols.lookup<func::FuncOp>(proposal.source.getHelper());
      llvm::DenseSet<Operation *> bindings;
      MapCorrespondence comparison(symbols, bindings, numericalRemaining);
      bool attempted = numericalRemaining != 0;
      if (attempted &&
          succeeded(comparison.check(proposal.source, proposal.function,
                                     helper.getBody().front())))
        continue;
      if (attempted && comparison.exhausted() == ComparisonCapacity::None)
        return diagnostics::emit(module.emitError(),
                                 "algebra-map-correspondence",
                                 "numerical map differs from its source");
      scope.selection(
          proposal.source, DecisionFamily::Lanes,
          RealizationChoice::Elementwise,
          OptimizationOutcome::exhausted(WorkOwner::OptionalComparison));
      declined.push_back(proposal);
      for (Operation &op : proposal.function.getBody().front())
        if (auto ref = op.getAttrOfType<FlatSymbolRefAttr>("binding"))
          if (auto binding =
                  symbols.lookup<local::OperationBindingOp>(ref.getValue());
              binding && protocol::numericalContract(binding.getContract()))
            declinedBindings.insert(binding);
    }
  }
  for (auto proposal : declined) {
    OpBuilder builder(proposal.function);
    auto retry = cast<algebra::MapRealizeOp>(builder.clone(*proposal.source));
    proposal.function.erase();
    if (failed(realizer.run(retry, *proposal.formula, scope,
                            NumericalExpressionMode::VectorOnly)))
      return failure();
  }
  for (Operation *binding : declinedBindings)
    if (SymbolTable::symbolKnownUseEmpty(binding, unit))
      binding->erase();
  scope.failure(VerificationDecision{VerificationObservation::Unclassified,
                                     "required map correspondence",
                                     {},
                                     {}});
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
