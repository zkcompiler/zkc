#include "CollectFold.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Interfaces/Collection.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
FailureOr<CollectFold> readCollectFold(Operation *producer, Operation *consumer,
                                       uint64_t &remaining) {
  auto charge = [&](uint64_t n) {
    if (n > remaining)
      return false;
    remaining -= n;
    return true;
  };
  if (!producer || !consumer || producer->getNextNode() != consumer ||
      !charge(1 + producer->getNumOperands() + consumer->getNumOperands()) ||
      !isComputation(producer) || !isComputation(consumer))
    return failure();
  CollectFold pair;
  if (failed(describe(producer, pair.producer)) ||
      failed(describe(consumer, pair.consumer)))
    return failure();
  auto &p = pair.producer;
  auto &c = pair.consumer;
  if (!p.total || !c.total || !p.collect || c.collect || p.predicate ||
      c.predicate || producer->getNumResults() != 1)
    return failure();
  auto collection =
      dyn_cast<CollectionTypeInterface>(producer->getResult(0).getType());
  if (!collection || !isa<algebra::FieldType>(collection.getElementType()) ||
      !isa<algebra::FieldVectorType, data::SequenceType>(
          producer->getResult(0).getType()))
    return failure();
  pair.collected = producer->getResult(0);
  for (auto &use : pair.collected.getUses())
    if (!charge(1) || use.getOwner() != consumer)
      return failure();
  auto parts = partitionEntry(c, consumer->getOperands());
  auto &domain = c.domain.getBody().front();
  if (failed(parts) || c.arguments != 1 || parts->domain[0] != pair.collected ||
      is_contained(parts->initialState, pair.collected) ||
      domain.front().getNextNode() != &domain.back() ||
      domain.getNumArguments() != 1)
    return failure();
  auto *constructor = &domain.front();
  pair.indexed = isa<data::DomainIndicesOp>(constructor);
  if ((!pair.indexed && !isa<data::DomainElementsOp>(constructor)) ||
      constructor->getNumOperands() != 1 || constructor->getNumResults() != 1 ||
      constructor->getOperand(0) != domain.getArgument(0) ||
      domain.back().getNumOperands() != 1 ||
      domain.back().getOperand(0) != constructor->getResult(0) ||
      (pair.indexed && cast<data::DomainIndicesOp>(constructor).getAxis() != 0))
    return failure();
  for (auto *helper : {p.helper, c.helper}) {
    if (!helper || helper->getNumRegions() != 1 ||
        !helper->getRegion(0).hasOneBlock())
      return failure();
    for (auto &op : helper->getRegion(0).front())
      if (!charge(1 + op.getNumOperands() + op.getNumResults()) ||
          op.getNumRegions() || isComputation(&op) || isa<func::CallOp>(op) ||
          (!isa<func::ReturnOp>(op) && !mathematical::isTotal(&op)))
        return failure();
  }
  auto callback = readCallbackABI(c, CallbackRole::Step);
  if (failed(callback) || callback->formals.items.size() != 1)
    return failure();
  auto environment =
      bindCallback(*callback, {parts->initialState, callback->formals.items,
                               parts->domain, parts->captures});
  if (failed(environment))
    return failure();
  for (auto [formal, actual] :
       zip(callback->entry->getArguments(), environment->actuals)) {
    if (actual != pair.collected)
      continue;
    for (auto &use : formal.getUses()) {
      auto read = dyn_cast<data::BoundedAtOp>(use.getOwner());
      if (!charge(1) || !pair.indexed || !read || use.getOperandNumber() != 0 ||
          read->getNumOperands() != 2 ||
          read->getOperand(1) != callback->formals.items[0])
        return failure();
    }
  }
  return pair;
}
} // namespace zkc::finite
