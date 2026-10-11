#include "LaneRealization.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Contracts/RingSharing.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
FailureOr<Value> realizeLanes(Block &formula,
                              const llvm::DenseMap<Value, LaneInput> &inputs,
                              Type vector, Value length, LaneEmitter emit) {
  auto field = dyn_cast<algebra::FieldType>(finite::elementType(vector));
  if (!field || formula.empty() || formula.back().getNumOperands() != 1)
    return failure();
  std::vector<ring::Input> slots;
  std::vector<ring::Node> nodes;
  llvm::DenseMap<Value, uint32_t> meanings;
  auto input = [&](Value value) {
    if (value.getType() != field || !inputs.contains(value))
      return;
    meanings[value] = nodes.size();
    nodes.push_back(ring::Node::slot(slots.size()));
    slots.push_back({field.getDomain().str()});
  };
  for (Value argument : formula.getArguments())
    input(argument);
  for (Operation &op : formula.without_terminator()) {
    if (op.getNumResults() != 1)
      return failure();
    Value result = op.getResult(0);
    if (inputs.contains(result)) {
      input(result);
      continue;
    }
    if (auto constant = finite::fieldConstant(&op)) {
      meanings[result] = nodes.size();
      nodes.push_back(ring::Node::literal(field.getDomain().str(), *constant));
      continue;
    }
    if (op.getNumOperands() != 2 || !meanings.contains(op.getOperand(0)) ||
        !meanings.contains(op.getOperand(1)))
      return failure();
    uint32_t left = meanings.lookup(op.getOperand(0)),
             right = meanings.lookup(op.getOperand(1));
    auto *contract = finite::semantics(&op);
    if (!contract ||
        contract->law.algebra != protocol::ComputationAlgebra::FieldRing ||
        !contract->law.total)
      return failure();
    if (contract->identity == MathematicalIdentity::FieldSubtract) {
      nodes.push_back(ring::Node::neg(right));
      right = nodes.size() - 1;
    } else if (contract->identity != MathematicalIdentity::FieldAdd &&
               contract->identity != MathematicalIdentity::FieldMultiply)
      return failure();
    meanings[result] = nodes.size();
    nodes.push_back(contract->identity == MathematicalIdentity::FieldMultiply
                        ? ring::Node::mul(left, right)
                        : ring::Node::add(left, right));
  }
  Value returned = formula.back().getOperand(0);
  if (!meanings.contains(returned))
    return failure();
  // Ring arenas contain exactly reachable nodes while their input inventory
  // retains unused slots. Admission above still inspected every instruction.
  std::vector<bool> needed(nodes.size(), false);
  needed[meanings.lookup(returned)] = true;
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
      std::move(slots), std::move(liveNodes), {meanings.lookup(returned)});
  if (!expression) {
    consumeError(expression.takeError());
    return failure();
  }
  auto shared = ring::shareExpression(*expression);
  if (!shared) {
    consumeError(shared.takeError());
    return failure();
  }
  if (auto error = ring::checkSharing(*expression, shared->expression,
                                      shared->nodeMap)) {
    consumeError(std::move(error));
    return failure();
  }

  // Only admitted pure ring instructions enter this window. Keep source SSA
  // order, sharing equal labeled nodes without algebraic code motion.
  llvm::DenseSet<Value> live{returned};
  for (Operation &op : llvm::reverse(formula.without_terminator()))
    if (live.contains(op.getResult(0)) && !inputs.contains(op.getResult(0)))
      live.insert(op.getOperands().begin(), op.getOperands().end());
  llvm::DenseMap<Value, LaneInput> values(inputs);
  llvm::DenseMap<uint32_t, LaneInput> representatives;
  for (auto [value, meaning] : meanings)
    if (auto found = inputs.find(value);
        meaning != UINT32_MAX && found != inputs.end())
      representatives[shared->nodeMap[meaning]] = found->second;
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
    if (!live.contains(result) || inputs.contains(result))
      continue;
    uint32_t meaning = shared->nodeMap[meanings.lookup(result)];
    if (auto found = representatives.find(meaning);
        found != representatives.end()) {
      values[result] = found->second;
      continue;
    }
    LaneInput realized;
    if (auto constant = finite::fieldConstant(&op))
      realized.value = emit("field.constant", {}, field, {*constant});
    else {
      LaneInput left = values.lookup(op.getOperand(0)),
                right = values.lookup(op.getOperand(1));
      if (!left.value || !right.value)
        return failure();
      const auto *contract = finite::semantics(&op);
      if (!contract || !contract->lanes)
        return failure();
      realized.lanes = left.lanes || right.lanes;
      if (!realized.lanes)
        realized.value =
            emit(contract->key, {left.value, right.value}, field, {});
      else if (!contract->lanes->mixed.empty() && left.lanes != right.lanes) {
        Value scalar = left.lanes ? right.value : left.value;
        Value lanes = left.lanes ? left.value : right.value;
        SmallVector<Value> operands{lanes, lanes};
        operands[contract->lanes->scalarOperand] = scalar;
        realized.value = emit(contract->lanes->mixed, operands, vector, {});
      } else
        realized.value = emit(contract->lanes->rows,
                              {broadcast(left), broadcast(right)}, vector, {});
    }
    if (!realized.value)
      return failure();
    values[result] = realized;
    representatives[meaning] = realized;
  }
  LaneInput result = values.lookup(returned);
  if (!result.value)
    return failure();
  return broadcast(result);
}
} // namespace zkc::mathematical
