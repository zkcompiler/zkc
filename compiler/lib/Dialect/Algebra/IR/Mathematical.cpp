#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Diagnostics.h"

using namespace mlir;

namespace zkc {
namespace {
LogicalResult refuse(Operation *op, llvm::StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", detail);
}

// Only nominal mathematical facts are consulted here. Profile admission and
// execution binding are separate clients of these reusable domain operations.
LogicalResult verifyField(Operation *op, bool equality) {
  auto lhs = cast<zkc::algebra::FieldType>(op->getOperand(0).getType());
  if (protocol::installedDomains().identitySort(lhs.getDomain()) != "Field" ||
      op->getOperand(1).getType() != lhs ||
      (!equality && op->getResult(0).getType() != lhs))
    return refuse(op, "expected operands and result in one admitted field");
  return success();
}

LogicalResult verifyGroup(Operation *op, bool equality, bool scalarAction) {
  auto lhs = cast<zkc::algebra::GroupType>(op->getOperand(0).getType());
  const auto &domains = protocol::installedDomains();
  if (domains.identitySort(lhs.getDomain()) != "Group" ||
      (!equality && op->getResult(0).getType() != lhs))
    return refuse(op, "expected an admitted group and matching result");
  if (scalarAction) {
    auto scalar = cast<zkc::algebra::FieldType>(op->getOperand(1).getType());
    if (domains.identitySort(scalar.getDomain()) != "Field" ||
        domains.associatedIdentity(lhs.getDomain(), "Scalar") !=
            scalar.getDomain())
      return refuse(op, "scalar action requires the group's associated field");
  } else if (op->getOperand(1).getType() != lhs) {
    return refuse(op, "expected both operands in the same group");
  }
  return success();
}
} // namespace

LogicalResult zkc::algebra::FieldAddOp::verify() {
  return verifyField(*this, false);
}
LogicalResult zkc::algebra::FieldMultiplyOp::verify() {
  return verifyField(*this, false);
}
LogicalResult zkc::algebra::FieldEqualOp::verify() {
  return verifyField(*this, true);
}
LogicalResult zkc::algebra::GroupAddOp::verify() {
  return verifyGroup(*this, false, false);
}
LogicalResult zkc::algebra::GroupScaleOp::verify() {
  return verifyGroup(*this, false, true);
}
LogicalResult zkc::algebra::GroupEqualOp::verify() {
  return verifyGroup(*this, true, false);
}
} // namespace zkc

namespace zkc::algebra {
std::optional<MathematicalIdentity> FieldAddOp::getMathematicalIdentity() {
  return MathematicalIdentity::FieldAdd;
}
llvm::SmallVector<unsigned>
FieldAddOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
std::optional<MathematicalIdentity> FieldMultiplyOp::getMathematicalIdentity() {
  return MathematicalIdentity::FieldMultiply;
}
llvm::SmallVector<unsigned>
FieldMultiplyOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
std::optional<MathematicalIdentity> FieldEqualOp::getMathematicalIdentity() {
  return MathematicalIdentity::FieldEqual;
}
llvm::SmallVector<unsigned>
FieldEqualOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
std::optional<MathematicalIdentity> GroupAddOp::getMathematicalIdentity() {
  return MathematicalIdentity::GroupAdd;
}
llvm::SmallVector<unsigned>
GroupAddOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
std::optional<MathematicalIdentity> GroupScaleOp::getMathematicalIdentity() {
  return MathematicalIdentity::GroupScale;
}
llvm::SmallVector<unsigned>
GroupScaleOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
std::optional<MathematicalIdentity> GroupEqualOp::getMathematicalIdentity() {
  return MathematicalIdentity::GroupEqual;
}
llvm::SmallVector<unsigned>
GroupEqualOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
} // namespace zkc::algebra

namespace zkc::algebra {
bool isFieldArray(Type type) {
  auto array = dyn_cast_if_present<RankedTensorType>(type);
  if (!array || array.getRank() != 1 || !array.hasStaticShape() ||
      array.getEncoding() || array.getDimSize(0) < 0 ||
      uint64_t(array.getDimSize(0)) > MaximumArrayLength)
    return false;
  auto element = dyn_cast<algebra::FieldType>(array.getElementType());
  return element && protocol::installedDomains().identitySort(
                        element.getDomain()) == "Field";
}
bool isCanonicalFieldLiteral(StringRef domain, StringRef value) {
  if (auto error =
          protocol::checkParameters("field.constant", {value.str()}, domain)) {
    consumeError(std::move(error));
    return false;
  }
  return true;
}
LogicalResult ConstantFieldOp::verify() {
  if (!isCanonicalFieldLiteral(getResult().getType().getDomain(), getValue()))
    return diagnostics::emit(emitOpError(), "mathematical-formation",
                             "expected a canonical field literal");
  return success();
}
LogicalResult ArrayAtOp::verify() {
  auto type = getArray().getType();
  auto index = getIndexAttr().getInt();
  if (!isFieldArray(type) || index < 0 || index >= type.getDimSize(0) ||
      type.getElementType() != getResult().getType())
    return diagnostics::emit(
        emitOpError(), "mathematical-formation",
        "expected static in-bounds field-array extraction");
  return success();
}
LogicalResult SubtractFieldOp::verify() { return verifyField(*this, false); }
std::optional<MathematicalIdentity> ConstantFieldOp::getMathematicalIdentity() {
  return MathematicalIdentity::FieldConstant;
}
SmallVector<unsigned> ConstantFieldOp::getOperandDependencies(unsigned) {
  return {};
}
std::optional<MathematicalIdentity> ArrayAtOp::getMathematicalIdentity() {
  return MathematicalIdentity::ArrayAt;
}
SmallVector<unsigned> ArrayAtOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity> SubtractFieldOp::getMathematicalIdentity() {
  return MathematicalIdentity::FieldSubtract;
}
SmallVector<unsigned> SubtractFieldOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
} // namespace zkc::algebra

namespace zkc::algebra {
LogicalResult PairingOp::verify() {
  const auto &domains = protocol::installedDomains();
  auto g1 = cast<GroupType>(getOperand(0).getType()).getDomain();
  auto g2 = cast<GroupType>(getOperand(1).getType()).getDomain();
  auto gt = cast<GroupType>(getResult().getType()).getDomain();
  auto field = domains.associatedIdentity(g1, "Scalar");
  if (field.empty() || !domains.hasFact("PairingField", {field.str()}) ||
      domains.associatedIdentity(field, "PairingG1") != g1 ||
      domains.associatedIdentity(field, "PairingG2") != g2 ||
      domains.associatedIdentity(field, "PairingGT") != gt)
    return diagnostics::emit(
        emitOpError(), "mathematical-formation",
        "expected the ordered source and target groups of one pairing");
  return success();
}
std::optional<MathematicalIdentity> PairingOp::getMathematicalIdentity() {
  return MathematicalIdentity::Pairing;
}
SmallVector<unsigned> PairingOp::getOperandDependencies(unsigned result) {
  if (result != 0)
    return {};
  return {0, 1};
}
} // namespace zkc::algebra
