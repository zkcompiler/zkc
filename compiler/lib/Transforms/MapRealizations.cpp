#include "ComputationSelection.h"
#include "LaneRealization.h"
#include "MapOccurrence.h"
#include "MathematicalComparison.h"
#include "MathematicalSupport.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/StructuredComputation.h"
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
emitMapPayload(algebra::MapRealizeOp map, Block &original, ValueRange inputs,
               MapPayloadForm form, MapEmitter emit,
               const SelectedReduction *dot) {
  auto shape =
      form == MapPayloadForm::Dot || form == MapPayloadForm::NumericalSum
          ? StructuredResult::Sum
          : StructuredResult::Map;
  auto structured =
      proposeStructuredComputation(original, map.getRowwise(), shape);
  if (!structured || failed(optimizeStructuredComputation(*structured)))
    return error("structured-computation", "candidate construction");
  auto scalar = consumeStructuredComputation(original, map.getRowwise(), shape,
                                             *structured);
  if (!scalar)
    return error("structured-computation", "candidate correspondence");
  Block &formula = scalar->front();
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
