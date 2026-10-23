#include "LaneRealization.h"
#include "FieldRegion.h"
#include "MathematicalRecipes.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
Expected<LaneFormulaResult>
admitLaneFormula(Block &formula, const llvm::DenseMap<Value, LaneInput> &inputs,
                 Type vector, uint64_t *remaining,
                 const MathematicalRecipes &recipes, Value output,
                 ValueRange additionalTerms, MathematicalIdentity combine) {
  auto unsupported = [] {
    return LaneFormulaResult{
        LaneRealizationStatus::Unsupported,
        {},
        "mathematical-lane-unsupported",
        {OptimizationStatus::Unsupported, OptimizationReason::LaneFormula}};
  };
  auto decline = OptimizationOutcome::exhausted(WorkOwner::Lanes);
  auto capacity = [&](StringRef reason) {
    return LaneFormulaResult{
        LaneRealizationStatus::Capacity, {}, reason.str(), decline};
  };
  // Bound all scans before allocating a Ring arena or emitting instructions.
  // Every charged step covers an operation and its operand/result slots; the
  // fixed multiplier covers the construction, liveness, sharing and emission
  // traversals. Ring's independent byte/node/depth limits still apply.
  auto charge = [&](uint64_t slots) {
    if (!remaining)
      return true;
    uint64_t cost = 8 * slots;
    if (cost > *remaining) {
      decline =
          OptimizationOutcome::exhausted(WorkOwner::Lanes, cost, *remaining);
      *remaining = 0;
      return false;
    }
    *remaining -= cost;
    return true;
  };
  if (!charge(formula.getNumArguments()))
    return capacity("mathematical-lane-work");
  for (Operation &op : formula)
    if (!charge(uint64_t(op.getNumOperands()) + op.getNumResults() + 1))
      return capacity("mathematical-lane-work");
  auto field = dyn_cast<algebra::FieldType>(finite::elementType(vector));
  if (!field || formula.empty() || formula.back().getNumOperands() != 1)
    return unsupported();
  Value returned = output ? output : formula.back().getOperand(0);
  if (returned.getType() != field)
    return unsupported();
  // Compute a borrowed SSA slice, but admit every instruction below before
  // dropping dead work. A reduction's combiner may lie outside this slice.
  SmallVector<Value> terms{returned};
  append_range(terms, additionalTerms);
  if (!additionalTerms.empty() && combine != MathematicalIdentity::FieldAdd &&
      combine != MathematicalIdentity::FieldMultiply)
    return unsupported();
  for (Value term : terms)
    if (term.getType() != field)
      return unsupported();
  if (!charge(additionalTerms.size()))
    return capacity("mathematical-lane-work");
  llvm::DenseSet<Value> live(terms.begin(), terms.end());
  for (Operation &op : llvm::reverse(formula.without_terminator())) {
    if (op.getNumResults() != 1)
      return unsupported();
    if (live.contains(op.getResult(0)) && !inputs.contains(op.getResult(0)))
      live.insert(op.getOperands().begin(), op.getOperands().end());
  }
  std::vector<ring::Input> slots;
  std::vector<ring::Node> nodes;
  SmallVector<LaneInput> slotBindings;
  llvm::DenseMap<Value, uint32_t> meanings;
  auto validBinding = [&](const LaneInput &input) {
    return input.value &&
           input.value.getType() == (input.lanes ? vector : Type(field));
  };
  auto input = [&](Value value) {
    if (value.getType() != field || !inputs.contains(value))
      return;
    meanings[value] = nodes.size();
    nodes.push_back(ring::Node::slot(slots.size()));
    slots.push_back({field.getDomain().str()});
    slotBindings.push_back(inputs.lookup(value));
  };
  for (Value argument : formula.getArguments())
    if (auto found = inputs.find(argument); found != inputs.end() &&
                                            argument.getType() == field &&
                                            !validBinding(found->second))
      return unsupported();
  for (Value argument : formula.getArguments())
    input(argument);
  for (Operation &op : formula.without_terminator()) {
    if (op.getNumResults() != 1)
      return unsupported();
    Value result = op.getResult(0);
    if (inputs.contains(result)) {
      if (result.getType() != field || !finite::replaceable(&op) ||
          !validBinding(inputs.lookup(result)))
        return unsupported();
      input(result);
      continue;
    }
    if (result.getType() != field || !finite::replaceable(&op))
      return unsupported();
    if (auto constant = finite::fieldConstant(&op)) {
      if (auto e = protocol::checkParameters("field.constant", {*constant},
                                             field.getDomain()))
        return std::move(e);
      // Ring literals are prime-subfield naturals. Other exact field values
      // enter through typed operands, never by reinterpreting bit patterns.
      if (!all_of(*constant, [](char c) { return isDigit(c); }))
        return unsupported();
      meanings[result] = nodes.size();
      nodes.push_back(ring::Node::literal(field.getDomain().str(), *constant));
      continue;
    }
    auto *contract = finite::semantics(&op);
    if (op.getNumOperands() != 2 || !contract ||
        contract->law.algebra != protocol::ComputationAlgebra::FieldRing ||
        !contract->law.total || !recipes.lane(contract->identity) ||
        !is_contained(
            ArrayRef<MathematicalIdentity>{MathematicalIdentity::FieldAdd,
                                           MathematicalIdentity::FieldSubtract,
                                           MathematicalIdentity::FieldMultiply},
            contract->identity))
      return unsupported();
    if (op.getOperand(0).getType() != field ||
        op.getOperand(1).getType() != field)
      return unsupported();
    if (!live.contains(result))
      continue;
    if (!meanings.contains(op.getOperand(0)) ||
        !meanings.contains(op.getOperand(1)))
      return unsupported();
    uint32_t left = meanings.lookup(op.getOperand(0)),
             right = meanings.lookup(op.getOperand(1));
    if (contract->identity == MathematicalIdentity::FieldSubtract) {
      nodes.push_back(ring::Node::neg(right));
      right = nodes.size() - 1;
    } else if (contract->identity != MathematicalIdentity::FieldAdd &&
               contract->identity != MathematicalIdentity::FieldMultiply)
      return unsupported();
    meanings[result] = nodes.size();
    nodes.push_back(contract->identity == MathematicalIdentity::FieldMultiply
                        ? ring::Node::mul(left, right)
                        : ring::Node::add(left, right));
  }
  for (Value term : terms)
    if (!meanings.contains(term))
      return unsupported();
  uint32_t outputNode = meanings.lookup(returned);
  for (Value term : additionalTerms) {
    nodes.push_back(combine == MathematicalIdentity::FieldMultiply
                        ? ring::Node::mul(outputNode, meanings.lookup(term))
                        : ring::Node::add(outputNode, meanings.lookup(term)));
    outputNode = nodes.size() - 1;
  }
  // Ring arenas contain exactly reachable nodes while their input inventory
  // retains unused slots. Admission above still inspected every instruction.
  std::vector<bool> needed(nodes.size(), false);
  needed[outputNode] = true;
  for (size_t i = nodes.size(); i-- > 0;)
    if (needed[i]) {
      const auto &node = nodes[i];
      if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
        needed[node.left] = true;
        needed[node.right] = true;
      } else if (node.kind == ring::Kind::Neg)
        needed[node.left] = true;
    }
  std::vector<uint32_t> liveMap(nodes.size(), UINT32_MAX);
  std::vector<ring::Node> liveNodes;
  for (uint32_t i = 0; i < nodes.size(); ++i) {
    if (!needed[i])
      continue;
    auto node = nodes[i];
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
      node.left = liveMap[node.left];
      node.right = liveMap[node.right];
    } else if (node.kind == ring::Kind::Neg)
      node.left = liveMap[node.left];
    liveMap[i] = liveNodes.size();
    liveNodes.push_back(std::move(node));
  }
  for (auto &entry : meanings)
    entry.second = liveMap[entry.second];
  auto expression = ring::Expression::create(
      std::move(slots), std::move(liveNodes), {liveMap[outputNode]});
  if (!expression) {
    std::string reason;
    auto error =
        handleErrors(expression.takeError(), [&](const Refusal &r) -> Error {
          if (r.code == "ring-limit" || r.code == "ring-depth") {
            reason = r.code;
            return Error::success();
          }
          return zkc::error(r.code, r.detail);
        });
    if (error)
      return std::move(error);
    return capacity(reason);
  }
  auto region = createFieldRegion(
      {formula, inputs, live, terms, slotBindings, combine}, field);
  if (!region)
    return region.takeError();
  LaneFormula admitted{std::move(*expression), std::move(slotBindings),
                       std::move(*region)};
  auto checked = checkFieldRegion(admitted);
  if (!checked)
    return checked.takeError();
  return LaneFormulaResult{
      LaneRealizationStatus::Realized, std::move(admitted), {}};
}

Expected<LaneRealizationResult>
emitVectorLanes(const LaneFormula &admitted, Type vector, Value length,
                const MathematicalRecipes &recipes, LaneEmitter emit) {
  auto invalid = [](StringRef reason) {
    return zkc::error("mathematical-lane-realization", reason);
  };
  auto checked = checkFieldRegion(admitted);
  if (!checked)
    return checked.takeError();
  auto module = *admitted.region;
  auto function = *module.getOps<func::FuncOp>().begin();
  auto generic = *function.getOps<linalg::GenericOp>().begin();
  Block &formula = generic.getRegion().front();
  auto field = cast<algebra::FieldType>(finite::elementType(vector));
  llvm::DenseMap<Value, LaneInput> values;
  for (auto [i, slot] : llvm::enumerate(admitted.slots)) {
    if (!slot.value ||
        slot.value.getType() != (slot.lanes ? vector : Type(field)))
      return invalid("structured region binding type changed");
    values[formula.getArgument(i)] = slot;
  }
  llvm::DenseMap<Value, Value> broadcasts;
  auto broadcast = [&](LaneInput value) {
    if (value.lanes)
      return value.value;
    auto &result = broadcasts[value.value];
    if (!result)
      result = emit("vector.fill", {value.value, length}, vector, {});
    return result;
  };
  for (Operation &op : formula.without_terminator()) {
    Value result = op.getResult(0);
    LaneInput realized;
    if (auto constant = finite::fieldConstant(&op))
      realized.value = emit("field.constant", {}, field, {*constant});
    else {
      LaneInput left = values.lookup(op.getOperand(0)),
                right = values.lookup(op.getOperand(1));
      if (!left.value || !right.value)
        return invalid("missing realized operand");
      const auto *contract = finite::semantics(&op);
      const auto *recipe =
          contract ? recipes.lane(contract->identity) : nullptr;
      if (!recipe)
        return invalid("missing selected lane recipe");
      realized.lanes = left.lanes || right.lanes;
      if (!realized.lanes)
        realized.value =
            emit(recipe->scalar, {left.value, right.value}, field, {});
      else if (!recipe->mixed.empty() && left.lanes != right.lanes) {
        Value scalar = left.lanes ? right.value : left.value;
        Value lanes = left.lanes ? left.value : right.value;
        SmallVector<Value> operands{lanes, lanes};
        operands[recipe->scalarOperand] = scalar;
        realized.value = emit(recipe->mixed, operands, vector, {});
      } else {
        LaneInput source[] = {left, right};
        realized.value = emit(recipe->rows,
                              {broadcast(source[recipe->first]),
                               broadcast(source[recipe->second])},
                              vector, {});
      }
    }
    if (!realized.value)
      return invalid("emitter returned no value");
    values[result] = realized;
  }
  LaneInput result = values.lookup(formula.back().getOperand(0));
  if (!result.value)
    return invalid("missing realized result");
  Value value = broadcast(result);
  if (!value)
    return invalid("broadcast returned no value");
  return LaneRealizationResult{LaneRealizationStatus::Realized, value, {}};
}
Expected<LaneRealizationResult> emitNumericalLanes(const LaneFormula &formula,
                                                   Type vector, Value rows,
                                                   LaneResultMode mode,
                                                   NumericalEmitter emit) {
  auto unsupported = [] {
    return LaneRealizationResult{
        LaneRealizationStatus::Unsupported,
        {},
        "mathematical-lane-unsupported",
        {OptimizationStatus::Unsupported, OptimizationReason::LaneFormula}};
  };
  auto capacity = [](StringRef reason) {
    return LaneRealizationResult{
        LaneRealizationStatus::Capacity,
        {},
        reason.str(),
        OptimizationOutcome::exhausted(WorkOwner::Lanes)};
  };
  if (formula.slots.size() > protocol::NumericalLimits::slots)
    return capacity("numerical-mask-limit");
  auto field = dyn_cast<algebra::FieldType>(finite::elementType(vector));
  if (!field || !rows || !rows.getType().isUnsignedInteger(64))
    return unsupported();
  auto expression = checkFieldRegion(formula);
  if (!expression)
    return expression.takeError();
  std::string mask;
  SmallVector<Value> operands{rows};
  for (const auto &slot : formula.slots) {
    if (!slot.value ||
        slot.value.getType() != (slot.lanes ? vector : Type(field)))
      return unsupported();
    mask += slot.lanes ? '1' : '0';
    operands.push_back(slot.value);
  }
  // An admitted identity map borrows its existing column. Domain guards and
  // eager arguments belong to the caller and have already been retained.
  const auto &root = expression->nodes()[expression->outputs()[0]];
  if (mode == LaneResultMode::Map && root.kind == ring::Kind::Input &&
      formula.slots[root.input].lanes)
    return LaneRealizationResult{
        LaneRealizationStatus::Realized, formula.slots[root.input].value, {}};
  std::string body = zkc::printJson(expression->encode());
  if (body.size() > protocol::NumericalLimits::bodyBytes)
    return capacity("numerical-body-limit");
  StringRef contract = mode == LaneResultMode::Map   ? "numerical.map"
                       : mode == LaneResultMode::Sum ? "numerical.sum"
                                                     : "numerical.product";
  protocol::BindingApplication binding{
      contract.str(), {field.getDomain().str(), mask}, ""};
  // Feasibility is checked before invoking the emitter, including exact
  // field/body/slot agreement. An invalid producer is an error, not fallback.
  if (auto e = protocol::checkNumericalParameters(binding, {body}))
    return std::move(e);
  Value value =
      emit(binding, operands,
           mode == LaneResultMode::Map ? vector : Type(field), {body});
  if (!value)
    return zkc::error("mathematical-lane-realization",
                      "emitter returned no value");
  return LaneRealizationResult{LaneRealizationStatus::Realized, value, {}};
}

Expected<LaneRealizationResult>
realizeLanes(Block &formula, const llvm::DenseMap<Value, LaneInput> &inputs,
             Type vector, Value length, uint64_t *remaining,
             const MathematicalRecipes &recipes, LaneEmitter emit,
             Value output) {
  auto admitted =
      admitLaneFormula(formula, inputs, vector, remaining, recipes, output);
  if (!admitted)
    return admitted.takeError();
  if (!admitted->formula)
    return LaneRealizationResult{
        admitted->status, {}, admitted->reason, admitted->outcome};
  return emitVectorLanes(*admitted->formula, vector, length, recipes, emit);
}
} // namespace zkc::mathematical
