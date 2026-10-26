#ifndef ZKC_TRANSFORMS_SCOPEDCOLLECTIONSUM_H
#define ZKC_TRANSFORMS_SCOPEDCOLLECTIONSUM_H

#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::finite {
// Structural eligibility only, over two adjacent admitted execution steps.
// Dispatch blocks are administrative CFG, not the source adjacency relation.
// Producer recognition and independent mathematical comparison remain separate.
inline mlir::Operation *
collectionSumConsumer(const protocol::SourceExecutionStep &producer,
                      const protocol::SourceExecutionStep *consumer,
                      const llvm::DenseSet<mlir::Operation *> *fixedBindings) {
  if (!mlir::isa<exec::CollectOp>(producer.operation) || !consumer ||
      !mlir::isa<exec::ApplyOp>(consumer->operation) ||
      producer.outputs.size() != 1 || consumer->inputs.size() != 1 ||
      consumer->outputs.size() != 1 ||
      consumer->inputs[0] != producer.outputs[0] ||
      !producer.outputs[0].hasOneUse() ||
      producer.outputs[0].use_begin()->getOwner() != consumer->operation)
    return nullptr;
  auto vector =
      mlir::dyn_cast<algebra::FieldVectorType>(producer.outputs[0].getType());
  auto call = mlir::cast<exec::ApplyOp>(consumer->operation);
  auto binding = mlir::SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
      call, call.getBindingAttr());
  if (!vector || consumer->outputs[0].getType() != vector.getElementType() ||
      !binding || binding.getContract() != "vector.sum" ||
      !binding.getImplementation().empty() ||
      (fixedBindings && fixedBindings->contains(binding)) ||
      !call.getParameters().empty() || binding.getArguments().size() != 1 ||
      binding.getArguments()[0] !=
          mlir::StringAttr::get(call.getContext(), vector.getDomain()))
    return nullptr;
  return call;
}
} // namespace zkc::finite
#endif
