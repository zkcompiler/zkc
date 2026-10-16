#include "zkc/Transforms/LinearContraction.h"
#include "mlir/IR/RegionKindInterface.h"

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
findLinearContractions(FunctionOpInterface function,
                       LinearContractionStats &stats) {
  llvm::SmallVector<LinearContractionGroup> groups;
  // Visit blocks in source order, including local control-flow bodies. A view
  // and all its consumers must remain in one block; no work is moved.
  if (function.isDeclaration() ||
      !llvm::hasSingleElement(function.getFunctionBody()))
    return groups;
  function->walk<WalkOrder::PreOrder>([&](Operation *operation) {
    if (operation->getParentOfType<FunctionOpInterface>() != function)
      return;
    if (mayBeGraphRegion(*operation->getParentRegion()))
      return;
    auto &op = *operation;
    auto producer = dyn_cast<DiagonalProducerInterface>(&op);
    if (!producer)
      return;
    ++stats.producers;
    auto production = producer.getDiagonalProducerRoles();
    if (!production || production->result >= op.getNumResults() ||
        production->factorsOperand >= op.getNumOperands() ||
        production->valuesOperand >= op.getNumOperands() ||
        production->factorsOperand == production->valuesOperand)
      return;
    Value result = op.getResult(production->result);
    if (result.use_empty() ||
        op.getOperand(production->valuesOperand).getType() != result.getType())
      return;
    LinearContractionGroup group{&op, *production, {}};
    bool compatible = true;
    // Operand uses, not distinct users: dot(v, v) must fail the values-slot
    // check. An immutable view can feed many contractions, never another map.
    for (OpOperand &use : result.getUses()) {
      Operation *user = use.getOwner();
      auto consumer = dyn_cast<DiagonalContractionInterface>(user);
      if (!consumer || user->getBlock() != op.getBlock() ||
          !op.isBeforeInBlock(user)) {
        compatible = false;
        break;
      }
      auto contraction = consumer.getDiagonalContractionRoles();
      if (!contraction ||
          use.getOperandNumber() != contraction->valuesOperand ||
          contraction->coefficientsOperand >= user->getNumOperands() ||
          contraction->coefficientsOperand == contraction->valuesOperand ||
          op.getOperand(production->factorsOperand).getType() !=
              user->getOperand(contraction->coefficientsOperand).getType()) {
        compatible = false;
        break;
      }
      group.uses.push_back({user, *contraction});
    }
    if (!compatible)
      return;
    // SSA use-list order is not source order. Binding names and budget choices
    // must be deterministic across import/clone/export paths.
    llvm::sort(group.uses, [](const auto &a, const auto &b) {
      return a.consumer->isBeforeInBlock(b.consumer);
    });
    ++stats.eligibleProducers;
    stats.eligiblePairs += group.uses.size();
    groups.push_back(std::move(group));
  });
  return groups;
}
} // namespace zkc
