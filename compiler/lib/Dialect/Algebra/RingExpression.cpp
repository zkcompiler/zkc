#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::algebra {
bool isRingOperation(Operation &op) {
  if (op.getNumRegions() || op.getNumResults() != 1)
    return false;
  auto field = dyn_cast<FieldType>(op.getResult(0).getType());
  if (!field)
    return false;
  if (isa<ConstantFieldOp>(op))
    return op.getAttrOfType<StringAttr>("value") && op.getAttrs().size() == 1 &&
           !op.getNumOperands();
  return isa<FieldAddOp, SubtractFieldOp, FieldMultiplyOp>(op) &&
         op.getAttrs().empty() && op.getNumOperands() == 2 &&
         op.getOperand(0).getType() == field &&
         op.getOperand(1).getType() == field;
}

Expected<ring::Expression> describeRingExpression(Block &block,
                                                  ValueRange results) {
  if (block.getNumArguments() > ring::Limits::inputs ||
      results.size() > ring::Limits::outputs || block.empty() ||
      !block.back().hasTrait<OpTrait::IsTerminator>())
    return zkc::error("ring-formula-shape");
  std::vector<ring::Input> inputs;
  std::vector<ring::Node> nodes;
  llvm::DenseMap<Value, uint32_t> values;
  for (auto arg : block.getArguments()) {
    auto field = dyn_cast<FieldType>(arg.getType());
    if (!field)
      return zkc::error("ring-formula-type");
    values[arg] = nodes.size();
    nodes.push_back(ring::Node::slot(inputs.size()));
    inputs.push_back({field.getDomain().str()});
  }
  for (auto &op : block.without_terminator()) {
    // Subtraction needs two arena nodes. Bound construction before allocation.
    if (nodes.size() > ring::Limits::nodes - 2)
      return zkc::error("ring-limit");
    if (!isRingOperation(op))
      return zkc::error("ring-formula-operation");
    auto field = cast<FieldType>(op.getResult(0).getType());
    if (isa<ConstantFieldOp>(op)) {
      auto value = op.getAttrOfType<StringAttr>("value");
      auto node =
          ring::Node::literal(field.getDomain().str(), value.getValue().str());
      // Check unused literals too; pruning cannot admit an invalid scalar body.
      auto checked = ring::Expression::create({}, {node}, {0});
      if (!checked)
        return checked.takeError();
      nodes.push_back(std::move(node));
    } else {
      auto left = values.find(op.getOperand(0));
      auto right = values.find(op.getOperand(1));
      if (left == values.end() || right == values.end())
        return zkc::error("ring-formula-capture");
      if (isa<FieldMultiplyOp>(op))
        nodes.push_back(ring::Node::mul(left->second, right->second));
      else if (isa<SubtractFieldOp>(op)) {
        nodes.push_back(ring::Node::neg(right->second));
        nodes.push_back(ring::Node::add(left->second, nodes.size() - 1));
      } else
        nodes.push_back(ring::Node::add(left->second, right->second));
    }
    values[op.getResult(0)] = nodes.size() - 1;
  }
  // Ring's canonical carrier contains no dead nodes. Preserve every input slot
  // independently: checked bulk clients still owe shape checks for unused
  // slots.
  std::vector<bool> live(nodes.size(), false);
  std::vector<uint32_t> outputs;
  for (auto result : results) {
    auto found = values.find(result);
    if (found == values.end())
      return zkc::error("ring-formula-capture");
    outputs.push_back(found->second);
    live[found->second] = true;
  }
  for (size_t i = nodes.size(); i-- > 0;) {
    if (!live[i])
      continue;
    const auto &node = nodes[i];
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
      live[node.left] = true;
      live[node.right] = true;
    } else if (node.kind == ring::Kind::Neg)
      live[node.left] = true;
  }
  std::vector<uint32_t> positions(nodes.size());
  std::vector<ring::Node> retained;
  for (size_t i = 0; i < nodes.size(); ++i) {
    if (!live[i])
      continue;
    auto node = nodes[i];
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
      node.left = positions[node.left];
      node.right = positions[node.right];
    } else if (node.kind == ring::Kind::Neg)
      node.left = positions[node.left];
    positions[i] = retained.size();
    retained.push_back(std::move(node));
  }
  for (auto &output : outputs)
    output = positions[output];
  return ring::Expression::create(std::move(inputs), std::move(retained),
                                  std::move(outputs));
}
} // namespace zkc::algebra
