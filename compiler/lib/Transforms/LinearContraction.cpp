#include "zkc/Transforms/LinearContraction.h"

using namespace mlir;
namespace zkc {
void printLinearContractionStats(const LinearContractionStats &stats,
                                 llvm::raw_ostream &out) {
  out << "linear-contractions: producers=" << stats.producers
      << " eligible=" << stats.eligiblePairs
      << " selected=" << stats.selectedPairs << '\n';
  out << "linear-contractions: eligible-producers=" << stats.eligibleProducers
      << " selected-producers=" << stats.selectedProducers << '\n';
}

llvm::SmallVector<LinearContractionGroup>
findLinearContractions(func::FuncOp function, LinearContractionStats &stats) {
  llvm::SmallVector<LinearContractionGroup> groups;
  // Protocol kernels live directly in one local function block. Do not infer
  // lifetime or observation behavior across regions, loops or function calls.
  if (function.isDeclaration() || !llvm::hasSingleElement(function.getBody()))
    return groups;
  for (auto &op : function.getBody().front()) {
    auto producer = dyn_cast<DiagonalProducerInterface>(&op);
    if (!producer)
      continue;
    ++stats.producers;
    auto production = producer.getDiagonalProducerSelection();
    if (!production || production->result >= op.getNumResults() ||
        production->factorsOperand >= op.getNumOperands() ||
        production->valuesOperand >= op.getNumOperands() ||
        production->factorsOperand == production->valuesOperand ||
        production->representation.empty())
      continue;
    Value result = op.getResult(production->result);
    if (result.use_empty() ||
        op.getOperand(production->valuesOperand).getType() != result.getType())
      continue;
    LinearContractionGroup group{&op, *production, {}};
    bool compatible = true;
    // Operand uses, not distinct users: dot(v, v) must fail the values-slot
    // check. An immutable view can feed many contractions, never another map.
    for (OpOperand &use : result.getUses()) {
      Operation *user = use.getOwner();
      auto consumer = dyn_cast<DiagonalContractionInterface>(user);
      if (!consumer || user->getBlock() != op.getBlock() ||
          user->getParentOp() != function.getOperation() ||
          !op.isBeforeInBlock(user)) {
        compatible = false;
        break;
      }
      auto contraction = consumer.getDiagonalContractionSelection();
      if (!contraction ||
          use.getOperandNumber() != contraction->valuesOperand ||
          contraction->coefficientsOperand >= user->getNumOperands() ||
          contraction->coefficientsOperand == contraction->valuesOperand ||
          production->representation != contraction->representation ||
          op.getOperand(production->factorsOperand).getType() !=
              user->getOperand(contraction->coefficientsOperand).getType()) {
        compatible = false;
        break;
      }
      group.uses.push_back({user, *contraction});
    }
    if (!compatible)
      continue;
    // SSA use-list order is not source order. Binding names and budget choices
    // must be deterministic across import/clone/export paths.
    llvm::sort(group.uses, [](const auto &a, const auto &b) {
      return a.consumer->isBeforeInBlock(b.consumer);
    });
    ++stats.eligibleProducers;
    stats.eligiblePairs += group.uses.size();
    groups.push_back(std::move(group));
  }
  return groups;
}
} // namespace zkc
