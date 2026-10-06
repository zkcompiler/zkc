#include "zkc/Dialect/Protocol/Semantics.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
std::optional<OperationSemantics> classify(Operation *op) {
  return llvm::TypeSwitch<Operation *, std::optional<OperationSemantics>>(op)
#define ZKC_MATH_OPERATION(OP, CATEGORY, CONTEXTS, ...)                        \
  .Case<OP>([](OP) -> std::optional<OperationSemantics> {                      \
    return OperationSemantics{Category::CATEGORY, CONTEXTS};                   \
  })
#include "zkc/Dialect/Protocol/MathematicalOperations.def"
#undef ZKC_MATH_OPERATION
      .Default(std::nullopt);
}
FailureOr<SmallVector<unsigned>> operandDependencies(Operation *op,
                                                     unsigned result) {
  auto refuse = [&](StringRef detail =
                        "expected each admitted scalar result to depend on all "
                        "operands exactly once in operand order")
      -> FailureOr<SmallVector<unsigned>> {
    diagnostics::emit(op->emitOpError(), "mathematical-dependencies", detail);
    return failure();
  };
  auto meaning = classify(op);
  if (!meaning || meaning->category != Category::Total ||
      result >= op->getNumResults())
    return refuse();
  SmallVector<unsigned> dependencies;
  if (auto model = dyn_cast<MathematicalOpInterface>(op)) {
    if (!model.getMathematicalIdentity())
      return refuse();
    dependencies = model.getOperandDependencies(result);
  } else {
    if (isa<arith::ConstantOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
            arith::CmpIOp, arith::SelectOp>(op))
      return refuse(
          "arith operation requires a registered mathematical interface; "
          "register it with registerMathematicalInterfaces");
    for (unsigned index = 0; index < op->getNumOperands(); ++index)
      dependencies.push_back(index);
  }
  if (dependencies.size() != op->getNumOperands())
    return refuse();
  for (auto [position, index] : llvm::enumerate(dependencies))
    if (index != position)
      return refuse();
  return dependencies;
}
LogicalResult verifyOperation(Operation *op, Context context) {
  auto meaning = classify(op);
  if (!meaning || !(meaning->contexts & context))
    return diagnostics::emit(
        op->emitOpError(), "mathematical-formation",
        "operation has no admitted meaning in this context");
  auto allowed = llvm::TypeSwitch<Operation *, ArrayRef<StringRef>>(op)
#define ZKC_MATH_OPERATION(OP, CATEGORY, CONTEXTS, ...)                        \
  .Case<OP>([](OP) -> ArrayRef<StringRef> {                                    \
    static const SmallVector<StringRef> attrs = {__VA_ARGS__};                 \
    return attrs;                                                              \
  })
#include "zkc/Dialect/Protocol/MathematicalOperations.def"
#undef ZKC_MATH_OPERATION
                     .Default(ArrayRef<StringRef>{});
  for (auto attribute : op->getAttrs())
    if (!llvm::is_contained(allowed, attribute.getName().getValue()))
      return diagnostics::emit(op->emitOpError(), "mathematical-formation",
                               "unsupported mathematical operation attribute");
  if (meaning->category == Category::Total)
    for (unsigned result = 0; result < op->getNumResults(); ++result)
      if (failed(operandDependencies(op, result)))
        return failure();
  return success();
}
} // namespace zkc::mathematical
