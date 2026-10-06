#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Interfaces/Mathematical.h"

using namespace mlir;
#include "zkc/Interfaces/Mathematical.cpp.inc"

namespace zkc {
namespace {
bool boolean(Type type) { return type.isSignlessInteger(1); }
bool selectedData(Type type) {
  return boolean(type) || isa<algebra::FieldType, algebra::GroupType>(type);
}

std::optional<MathematicalIdentity> arithIdentity(Operation *op) {
  if (op->getNumResults() != 1)
    return std::nullopt;
  if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
    auto value = dyn_cast<IntegerAttr>(constant.getValue());
    if (boolean(constant.getType()) && value && boolean(value.getType()))
      return MathematicalIdentity::BooleanConstant;
    return std::nullopt;
  }
  if (auto select = dyn_cast<arith::SelectOp>(op)) {
    if (boolean(select.getCondition().getType()) &&
        selectedData(select.getType()) &&
        select.getTrueValue().getType() == select.getType() &&
        select.getFalseValue().getType() == select.getType())
      return MathematicalIdentity::Select;
    return std::nullopt;
  }
  if (op->getNumOperands() != 2 || !boolean(op->getResult(0).getType()) ||
      !llvm::all_of(op->getOperandTypes(), boolean))
    return std::nullopt;
  if (isa<arith::AndIOp>(op))
    return MathematicalIdentity::BooleanAnd;
  if (isa<arith::OrIOp>(op))
    return MathematicalIdentity::BooleanOr;
  if (isa<arith::XOrIOp>(op))
    return MathematicalIdentity::BooleanXor;
  if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
    if (compare.getPredicate() == arith::CmpIPredicate::eq)
      return MathematicalIdentity::BooleanEqual;
    if (compare.getPredicate() == arith::CmpIPredicate::ne)
      return MathematicalIdentity::BooleanNotEqual;
  }
  return std::nullopt;
}

template <typename Op>
struct ArithModel final
    : MathematicalOpInterface::ExternalModel<ArithModel<Op>, Op> {
  std::optional<MathematicalIdentity>
  getMathematicalIdentity(Operation *op) const {
    return arithIdentity(op);
  }

  llvm::SmallVector<unsigned> getOperandDependencies(Operation *op,
                                                     unsigned result) const {
    if (result >= op->getNumResults() || !arithIdentity(op))
      return {};
    llvm::SmallVector<unsigned> dependencies;
    for (unsigned i = 0; i < op->getNumOperands(); ++i)
      dependencies.push_back(i);
    return dependencies;
  }
};
struct ArrayModel final
    : MathematicalOpInterface::ExternalModel<ArrayModel,
                                             tensor::FromElementsOp> {
  std::optional<MathematicalIdentity>
  getMathematicalIdentity(Operation *op) const {
    if (!algebra::isFieldArray(op->getResult(0).getType()))
      return std::nullopt;
    return MathematicalIdentity::ArrayFromElements;
  }
  llvm::SmallVector<unsigned> getOperandDependencies(Operation *op,
                                                     unsigned result) const {
    llvm::SmallVector<unsigned> indices;
    if (result == 0)
      for (unsigned i = 0; i < op->getNumOperands(); ++i)
        indices.push_back(i);
    return indices;
  }
};
} // namespace

void registerMathematicalInterfaces(DialectRegistry &registry) {
  registry.addExtension(+[](MLIRContext *context, tensor::TensorDialect *) {
    tensor::FromElementsOp::attachInterface<ArrayModel>(*context);
  });
  registry.addExtension(+[](MLIRContext *context, arith::ArithDialect *) {
    arith::ConstantOp::attachInterface<ArithModel<arith::ConstantOp>>(*context);
    arith::AndIOp::attachInterface<ArithModel<arith::AndIOp>>(*context);
    arith::OrIOp::attachInterface<ArithModel<arith::OrIOp>>(*context);
    arith::XOrIOp::attachInterface<ArithModel<arith::XOrIOp>>(*context);
    arith::CmpIOp::attachInterface<ArithModel<arith::CmpIOp>>(*context);
    arith::SelectOp::attachInterface<ArithModel<arith::SelectOp>>(*context);
  });
}
} // namespace zkc
