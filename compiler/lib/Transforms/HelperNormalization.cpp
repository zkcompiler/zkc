#include "HelperNormalization.h"
#include "Computation/Support.h"
#include "MathematicalSupport.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Interfaces/Collection.h"

using namespace mlir;
namespace zkc::mathematical {
LogicalResult foldArrayProjections(Block &body, uint64_t &work,
                                   OptimizationOutcome *outcome) {
  for (auto &op : llvm::make_early_inc_range(body)) {
    if (!finite::consumeComputationWork(work, 1, WorkOwner::Structural,
                                        outcome))
      return failure();
    if (auto projection = dyn_cast<data::ArrayAtOp>(op)) {
      SmallVector<Attribute> attributes(projection->getNumOperands());
      auto folded = projection.fold({attributes, projection});
      if (auto value = dyn_cast_if_present<Value>(folded)) {
        projection.getResult().replaceAllUsesWith(value);
        projection.erase();
      }
    }
  }
  // Do not erase unused arithmetic, nested computations or admission actions.
  for (auto &op : llvm::make_early_inc_range(llvm::reverse(body))) {
    if (!finite::consumeComputationWork(work, 1, WorkOwner::Structural,
                                        outcome))
      return failure();
    if (isa<data::ArrayFromElementsOp>(op) && op.use_empty())
      op.erase();
  }
  return success();
}

CheckedHelperNormalizations::CheckedHelperNormalizations(Operation *root)
    : root(root), checker(root), provenance(root) {}

LogicalResult CheckedHelperNormalizations::readback(uint64_t *remaining) {
  auto &budget = remaining ? *remaining : work;
  for (auto function : root->getRegion(0).front().getOps<func::FuncOp>()) {
    auto snapshot = computation::exactReadback(function, root, budget);
    if (!snapshot ||
        failed(provenance.checkExpansion(function, snapshot->front())))
      return diagnostics::emit(
          function.emitError(), "kernel-recipe-subset",
          "exact helper readback failed or exceeded its bound");
    bodies.try_emplace(function, std::move(snapshot));
  }
  return success();
}

LogicalResult CheckedHelperNormalizations::prepare(Operation *source) {
  SmallVector<Operation *> pending{source};
  while (!pending.empty()) {
    auto *current = pending.pop_back_val();
    if (!work)
      return diagnostics::emit(source->emitOpError(),
                               "mathematical-helper-limit",
                               "normalization proposal work bound");
    --work;
    if (!visited.insert(current).second)
      continue;
    if (auto helper = dyn_cast<func::FuncOp>(current)) {
      // Charge before cloning, and share every producer budget over the
      // complete collection of helpers. Proposals become usable only after
      // the independent reader has compared all result coordinates.
      if (failed(chargeHelperOperations(helper, operations, indices, &work)))
        return failure();
      OwningOpRef<func::FuncOp> proposal(cast<func::FuncOp>(helper->clone()));
      if (failed(inlineHelpers(*proposal, operations, indices, symbols, root,
                               &work)) ||
          failed(provenance.checkExpansion(helper, proposal->front())) ||
          failed(chargeHelperOperations(*proposal, snapshotOperations,
                                        snapshotIndices, &work)))
        return failure();
      OwningOpRef<func::FuncOp> expanded(
          cast<func::FuncOp>((*proposal)->clone()));
      SmallVector<Operation *> generated;
      if (failed(poly::eliminatePolynomials(proposal->front(), polynomial)) ||
          failed(provenance.checkNormalization(*expanded, proposal->front(),
                                               &generated)))
        return failure();
      if (!computation::chargeCopy(*proposal, work))
        return failure();
      OwningOpRef<func::FuncOp> unsimplified(
          cast<func::FuncOp>((*proposal)->clone()));
      // Simplify only inside the admitted total mathematical closure, before
      // ordered concrete ports or executable recipes are selected. The
      // independent meaning reader checks the final result coordinates too.
      auto &body = proposal->front();
      OpBuilder builder(helper.getContext());
      for (auto dim : llvm::make_early_inc_range(body.getOps<data::DimOp>())) {
        if (!work)
          return failure();
        --work;
        auto type = cast<CollectionTypeInterface>(dim.getInput().getType());
        auto extent = type.getStaticExtent(dim.getAxisAttr().getInt());
        if (!extent)
          continue;
        builder.setInsertionPoint(dim);
        auto index = data::IndexOp::create(
            builder, dim.getLoc(), dim.getOutput().getType(),
            builder.getIntegerAttr(builder.getIntegerType(64, false), *extent));
        dim.getOutput().replaceAllUsesWith(index.getOutput());
        dim.erase();
      }
      if (failed(foldArrayProjections(body, work)))
        return failure();
      for (auto &op : llvm::make_early_inc_range(llvm::reverse(body))) {
        if (!work)
          return failure();
        --work;
        if (isTotal(&op) && !finite::isComputation(&op) && op.use_empty())
          op.erase();
      }
      if (failed(provenance.checkSimplification(*unsimplified, body)) ||
          failed(checker.check(helper, body)))
        return failure();
      llvm::DenseSet<Operation *> origins(generated.begin(), generated.end());
      for (auto &op : body)
        if (origins.contains(&op))
          polynomialGenerated.insert(&op);
      current = proposal->getOperation();
      bodies.try_emplace(helper, std::move(proposal));
    }
    auto walk = current->walk([&](Operation *op) {
      uint64_t amount = 1 + op->getNumOperands() + op->getNumResults();
      if (amount > work) {
        work = 0;
        diagnostics::emit(source->emitOpError(), "mathematical-helper-limit",
                          "normalization proposal work bound");
        return WalkResult::interrupt();
      }
      work -= amount;
      if (!finite::isComputation(op))
        return WalkResult::advance();
      finite::Computation computation;
      if (failed(finite::describe(op, computation, root, &symbols)))
        return WalkResult::interrupt();
      if (computation.total) {
        pending.push_back(computation.helper);
        if (computation.predicate)
          pending.push_back(computation.predicate);
      }
      return WalkResult::advance();
    });
    if (walk.wasInterrupted())
      return failure();
  }
  return success();
}
func::FuncOp CheckedHelperNormalizations::lookup(Operation *helper) const {
  auto found = bodies.find(helper);
  return found == bodies.end() ? func::FuncOp() : *found->second;
}
} // namespace zkc::mathematical
