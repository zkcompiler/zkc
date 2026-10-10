#include "MathematicalSupport.h"
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
#include "llvm/ADT/StringSet.h"
#include <map>
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

// A formula value either holds one scalar shared by every row or one value per
// row. Vector results of a realization always have the common row count.
enum class Mode { Scalar, Rows };

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
              uint64_t &indices, uint64_t *work = nullptr) {
  auto helper = symbols.lookupSymbolIn<func::FuncOp>(unit, map.getHelperAttr());
  if (!helper || helper.isExternal() || !helper.getBody().hasOneBlock()) {
    diagnostics::emit(map.emitOpError(), "algebra-map-helper",
                      "expected a helper body");
    return failure();
  }
  if (failed(chargeHelperOperations(helper, remaining, indices, work)))
    return failure();
  OwningOpRef<func::FuncOp> scratch(cast<func::FuncOp>(helper->clone()));
  if (failed(inlineHelpers(*scratch, remaining, indices, symbols, unit, work)))
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

// Operations whose result reaches the formula result, in SSA order. The Ring
// view has already checked the others; removing them preserves the value of a
// formula built only from constants, addition, subtraction and multiplication.
SmallVector<Operation *> liveOperations(Block &formula) {
  llvm::DenseSet<Value> needed(formula.back().getOperands().begin(),
                               formula.back().getOperands().end());
  SmallVector<Operation *> live;
  for (auto &op : llvm::reverse(formula.without_terminator())) {
    if (!llvm::any_of(op.getResults(),
                      [&](Value value) { return needed.contains(value); }))
      continue;
    live.push_back(&op);
    needed.insert(op.getOperands().begin(), op.getOperands().end());
  }
  std::reverse(live.begin(), live.end());
  return live;
}

StringRef contractSuffix(Operation *op) {
  return isa<algebra::FieldAddOp>(op)        ? "add"
         : isa<algebra::SubtractFieldOp>(op) ? "sub"
                                             : "mul";
}

// Lower a checked map with O(formula) operations, independent of the runtime
// row count. Scalar subexpressions stay scalar. A scalar meets rows through
// vector.scale for multiplication; for addition and subtraction its broadcast
// vector.fill(scalar, rows) is emitted immediately before the first operation
// that needs it and reused afterwards. A scalar result is broadcast likewise.
class MapRealizer {
  protocol_ir::ProtocolModuleOp unit;
  OpBuilder builder;
  llvm::StringSet<> names;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;
  unsigned nextName = 0, nextSite = 0;
  Location loc;
  algebra::FieldType field;
  Type index, boolean, vector;
  Value rows;
  llvm::DenseMap<Value, Value> broadcasts;

  FlatSymbolRefAttr binding(StringRef contract,
                            ArrayRef<std::string> arguments) {
    auto key = std::make_pair(
        contract.str(),
        std::vector<std::string>(arguments.begin(), arguments.end()));
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      std::string name;
      do {
        name = "_map_binding_" + std::to_string(nextName++);
      } while (!names.insert(name).second);
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(&unit.getBody().front());
      SmallVector<Attribute> args;
      for (const auto &arg : arguments)
        args.push_back(builder.getStringAttr(arg));
      local::OperationBindingOp::create(builder, loc, name, contract,
                                        builder.getArrayAttr(args), "");
      found = bindings.emplace(std::move(key), name).first;
    }
    return FlatSymbolRefAttr::get(builder.getContext(), found->second);
  }
  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> parameters = {}) {
    SmallVector<std::string> arguments;
    if (!boundWithoutField(contract))
      arguments.push_back(field.getDomain().str());
    OperationState state(loc, protocol::boundOperationName(contract));
    state.addOperands(inputs);
    if (output)
      state.addTypes(output);
    state.addAttribute("binding", binding(contract, arguments));
    state.addAttribute(
        "site", builder.getStringAttr("map_" + std::to_string(nextSite++)));
    SmallVector<Attribute> attrs;
    for (const auto &parameter : parameters)
      attrs.push_back(builder.getStringAttr(parameter));
    state.addAttribute("parameters", builder.getArrayAttr(attrs));
    auto *op = builder.create(state);
    return output ? op->getResult(0) : Value();
  }
  Value broadcast(Value scalar) {
    auto &found = broadcasts[scalar];
    if (!found)
      found = emit("vector.fill", {scalar, rows}, vector);
    return found;
  }

public:
  explicit MapRealizer(protocol_ir::ProtocolModuleOp unit)
      : unit(unit), builder(unit.getContext()), loc(unit.getLoc()) {
    for (auto &op : unit.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  void run(algebra::MapRealizeOp map, Block &formula) {
    loc = map.getLoc();
    nextSite = 0;
    broadcasts.clear();
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
    llvm::DenseMap<Value, std::pair<Mode, Value>> values;
    for (auto [i, argument] : llvm::enumerate(formula.getArguments()))
      values[argument] = {rowwise[i] ? Mode::Rows : Mode::Scalar,
                          entry->getArgument(i)};
    for (Operation *op : liveOperations(formula)) {
      std::pair<Mode, Value> result{Mode::Scalar, Value()};
      if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
        result.second =
            emit("field.constant", {}, field, {constant.getValue().str()});
      } else {
        auto [leftMode, left] = values.lookup(op->getOperand(0));
        auto [rightMode, right] = values.lookup(op->getOperand(1));
        auto suffix = contractSuffix(op);
        if (leftMode == Mode::Scalar && rightMode == Mode::Scalar) {
          result.second = emit(("field." + suffix).str(), {left, right}, field);
        } else if (suffix == "mul" &&
                   (leftMode == Mode::Scalar || rightMode == Mode::Scalar)) {
          result = {Mode::Rows,
                    leftMode == Mode::Rows
                        ? emit("vector.scale", {left, right}, vector)
                        : emit("vector.scale", {right, left}, vector)};
        } else {
          if (leftMode == Mode::Scalar)
            left = broadcast(left);
          if (rightMode == Mode::Scalar)
            right = broadcast(right);
          result = {Mode::Rows,
                    emit(("vector." + suffix).str(), {left, right}, vector)};
        }
      }
      values[op->getResult(0)] = result;
    }
    auto [mode, value] = values.lookup(formula.back().getOperand(0));
    if (mode == Mode::Scalar)
      value = broadcast(value);
    local::ReturnOp::create(builder, loc, value);
    map.erase();
  }
};

// Read one generated body against the scalar formula. Values are actual
// candidate SSA values; this checker never builds IR or calls the realizer.
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
  llvm::DenseMap<Value, Value> broadcasts;

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
  Value broadcast(Value scalar) {
    auto &found = broadcasts[scalar];
    if (!found)
      found = primitive("vector.fill", {scalar, rows}, vector);
    return found;
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
    llvm::DenseMap<Value, std::pair<Mode, Value>> values;
    for (auto [i, argument] : llvm::enumerate(formula.getArguments()))
      values[argument] = {rowwise[i] ? Mode::Rows : Mode::Scalar,
                          entry.getArgument(i)};
    for (Operation *op : liveOperations(formula)) {
      if (!valid || !remaining)
        return failure();
      --remaining;
      std::pair<Mode, Value> result{Mode::Scalar, Value()};
      if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
        result.second =
            primitive("field.constant", {}, field, {constant.getValue().str()});
      } else if (isa<algebra::FieldAddOp, algebra::SubtractFieldOp,
                     algebra::FieldMultiplyOp>(op)) {
        auto left = values.find(op->getOperand(0));
        auto right = values.find(op->getOperand(1));
        if (left == values.end() || right == values.end())
          return failure();
        auto [leftMode, leftValue] = left->second;
        auto [rightMode, rightValue] = right->second;
        StringRef suffix = isa<algebra::FieldAddOp>(op)        ? "add"
                           : isa<algebra::SubtractFieldOp>(op) ? "sub"
                                                               : "mul";
        bool leftRows = leftMode == Mode::Rows,
             rightRows = rightMode == Mode::Rows;
        if (!leftRows && !rightRows)
          result.second = primitive(("field." + suffix).str(),
                                    {leftValue, rightValue}, field);
        else if (suffix == "mul" && leftRows != rightRows)
          // Field multiplication is commutative; the scaled rows come first.
          result = {Mode::Rows, primitive("vector.scale",
                                          {leftRows ? leftValue : rightValue,
                                           leftRows ? rightValue : leftValue},
                                          vector)};
        else {
          if (!leftRows)
            leftValue = broadcast(leftValue);
          if (!rightRows)
            rightValue = broadcast(rightValue);
          result = {Mode::Rows, primitive(("vector." + suffix).str(),
                                          {leftValue, rightValue}, vector)};
        }
      } else
        return failure();
      if (!valid)
        return failure();
      values[op->getResult(0)] = result;
    }
    auto found = values.find(formula.back().getOperand(0));
    if (found == values.end())
      return failure();
    auto [mode, value] = found->second;
    if (mode == Mode::Scalar)
      value = broadcast(value);
    if (!valid || !cursor || !isa<local::ReturnOp>(cursor) ||
        cursor->getNextNode() || !cursor->getAttrs().empty() ||
        !llvm::equal(cursor->getOperands(), ValueRange{value}))
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
  SymbolTableCollection originalSymbols;
  llvm::DenseSet<Operation *> retained, bindings;
  uint64_t remaining = 1000000, indices = 1000000;
  unsigned helpers = realizedHelperOperationLimit;
  for (Operation &op : before->getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    if (!name)
      return refuse("unnamed declaration");
    Operation *replacement = symbols.lookup(name.getValue());
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    if (auto map = dyn_cast<algebra::MapRealizeOp>(op)) {
      // The reference formula is derived again from the retained original.
      auto function = dyn_cast<local::FuncOp>(replacement);
      auto formula =
          scalarFormula(map, *before, originalSymbols, helpers, indices);
      if (!function || failed(formula))
        return refuse("realization declaration or formula");
      if (failed(MapCorrespondence(symbols, bindings, remaining)
                     .check(map, function, (*formula)->front())))
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

LogicalResult expandMapRealizations(ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  auto original = protocolUnit(module);
  if (failed(original))
    return diagnostics::emit(module.emitError(), "algebra-map-context",
                             "expected the 'protocol' profile");
  if (original->getBody().front().getOps<algebra::MapRealizeOp>().empty())
    return success();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  auto unit = *protocolUnit(*candidate);
  // Derive every formula before editing the candidate's symbol table.
  SmallVector<std::pair<algebra::MapRealizeOp, OwningOpRef<func::FuncOp>>> maps;
  {
    SymbolTableCollection symbols;
    unsigned helpers = realizedHelperOperationLimit;
    uint64_t indices = 1000000;
    for (auto map : unit.getBody().front().getOps<algebra::MapRealizeOp>()) {
      auto formula = scalarFormula(map, unit, symbols, helpers, indices);
      if (failed(formula))
        return failure();
      maps.emplace_back(map, std::move(*formula));
    }
  }
  MapRealizer realizer(unit);
  for (auto &[map, formula] : maps)
    realizer.run(map, formula->front());
  if (failed(verifyMapRealizationsPreserved(module, *candidate)))
    return diagnostics::emit(module.emitError(), "algebra-map-lowering",
                             "realized map failed its correspondence check");
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}

FailureOr<std::map<std::string, std::pair<unsigned, unsigned>>>
describeMapProducts(ModuleOp module) {
  auto unit = protocolUnit(module);
  if (failed(unit))
    return failure();
  std::map<std::string, std::pair<unsigned, unsigned>> products;
  SymbolTableCollection symbols;
  unsigned helpers = realizedHelperOperationLimit;
  uint64_t indices = 1000000;
  for (auto map : unit->getBody().front().getOps<algebra::MapRealizeOp>()) {
    auto formula = scalarFormula(map, *unit, symbols, helpers, indices);
    if (failed(formula))
      return failure();
    auto &body = (*formula)->front();
    auto product =
        body.back().getOperand(0).getDefiningOp<algebra::FieldMultiplyOp>();
    if (!product)
      continue;
    auto left = dyn_cast<BlockArgument>(product->getOperand(0));
    auto right = dyn_cast<BlockArgument>(product->getOperand(1));
    if (left && right && left.getOwner() == &body &&
        right.getOwner() == &body && map.getRowwise()[left.getArgNumber()] &&
        map.getRowwise()[right.getArgNumber()])
      products.emplace(
          map.getSymName().str(),
          std::make_pair(left.getArgNumber(), right.getArgNumber()));
  }
  return products;
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
