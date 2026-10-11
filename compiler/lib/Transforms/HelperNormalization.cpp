#include "HelperNormalization.h"
#include "MathematicalSupport.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Interfaces/Collection.h"

using namespace mlir;
namespace zkc::mathematical {
CheckedHelperNormalizations::CheckedHelperNormalizations(Operation *root)
    : root(root), checker(root) {}

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
          failed(poly::eliminatePolynomials(proposal->front(), polynomial)) ||
          failed(checker.check(helper, proposal->front())))
        return failure();
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
LogicalResult
CheckedHelperNormalizations::prepareRealization(func::FuncOp helper) {
  if (realizations.contains(helper))
    return success();
  if (failed(prepare(helper)))
    return failure();
  auto normalized = lookup(helper);
  if (!normalized ||
      failed(chargeHelperOperations(normalized, snapshotOperations,
                                    snapshotIndices, &work)))
    return failure();
  OwningOpRef<func::FuncOp> proposal(cast<func::FuncOp>(normalized->clone()));
  auto &body = proposal->front();
  OpBuilder builder(helper.getContext());
  for (auto dim : llvm::make_early_inc_range(body.getOps<data::DimOp>())) {
    auto type = cast<CollectionTypeInterface>(dim.getInput().getType());
    auto axis = dim.getAxisAttr().getInt();
    auto extent = type.getStaticExtent(axis);
    if (!extent)
      continue;
    builder.setInsertionPoint(dim);
    auto index =
        data::IndexOp::create(builder, dim.getLoc(), dim.getOutput().getType(),
                              builder.getStringAttr(std::to_string(*extent)));
    dim.getOutput().replaceAllUsesWith(index.getOutput());
    dim.erase();
  }
  for (auto &op : llvm::make_early_inc_range(llvm::reverse(body)))
    if (isTotal(&op) && op.use_empty())
      op.erase();
  if (failed(checker.check(helper, body)))
    return failure();
  realizations.try_emplace(helper, std::move(proposal));
  return success();
}
func::FuncOp CheckedHelperNormalizations::lookup(Operation *helper,
                                                 bool realization) const {
  const auto &cache = realization ? realizations : bodies;
  auto found = cache.find(helper);
  return found == cache.end() ? func::FuncOp() : *found->second;
}
} // namespace zkc::mathematical
