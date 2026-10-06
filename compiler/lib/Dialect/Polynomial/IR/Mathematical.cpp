#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MathExtras.h"
#include <limits>

using namespace mlir;
using namespace llvm;
namespace zkc::poly {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "polynomial-formation", detail);
}
algebra::FieldType field(Type type) {
  if (auto polynomial = dyn_cast<PolynomialType>(type))
    return algebra::FieldType::get(type.getContext(), polynomial.getDomain());
  if (auto array = dyn_cast<RankedTensorType>(type))
    return dyn_cast<algebra::FieldType>(array.getElementType());
  return dyn_cast<algebra::FieldType>(type);
}
LogicalResult sameField(Operation *op) {
  algebra::FieldType expected;
  SmallVector<Type> types(op->getOperandTypes());
  llvm::append_range(types, op->getResultTypes());
  for (auto type : types) {
    auto actual = field(type);
    if (!actual || (expected && actual != expected))
      return refuse(op, "expected one field for every operand and result");
    expected = actual;
    if (isa<RankedTensorType>(type) &&
        (!algebra::isFieldArray(type) ||
         cast<RankedTensorType>(type).getDimSize(0) == 0))
      return refuse(op, "expected a positive static rank-one field tensor");
  }
  return success();
}
uint64_t length(Type type) {
  return cast<RankedTensorType>(type).getDimSize(0);
}
LogicalResult binary(Operation *op) {
  if (failed(sameField(op)))
    return failure();
  if (op->getOperand(0).getType() != op->getOperand(1).getType() ||
      op->getOperand(0).getType() != op->getResult(0).getType())
    return refuse(op,
                  "polynomial operands and result must have the same arity");
  return success();
}
SmallVector<unsigned> allOperands(Operation *op, unsigned result) {
  SmallVector<unsigned> values;
  if (result < op->getNumResults())
    for (unsigned i = 0; i < op->getNumOperands(); ++i)
      values.push_back(i);
  return values;
}
} // namespace

LogicalResult verifyDomain(Operation *owner, StringRef domain,
                           ArrayAttr points) {
  if (!points || points.empty() || points.size() > MaximumDomainLength)
    return refuse(owner, "expected 1..64 ordered domain points");
  llvm::StringSet<> seen;
  for (auto point : points) {
    auto value = dyn_cast<StringAttr>(point);
    if (!value || !algebra::isCanonicalFieldLiteral(domain, value.getValue()) ||
        !seen.insert(value.getValue()).second)
      return refuse(owner,
                    "domain points must be distinct canonical field literals");
  }
  return success();
}
LogicalResult
PolynomialType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                       StringRef domain, uint64_t arity) {
  if (protocol::installedDomains().identitySort(domain) != "Field" ||
      arity > MaximumPolynomialArity)
    return diagnostics::emit(
        emit(), "polynomial-formation",
        "expected an installed field and arity at most 32");
  return success();
}
LogicalResult ConstantPolynomialOp::verify() { return sameField(*this); }
LogicalResult CoefficientPolynomialOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  if (getPolynomial().getType().getArity() != 1)
    return refuse(*this, "coefficient construction is univariate");
  return success();
}
LogicalResult MultilinearPolynomialOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  auto arity = getPolynomial().getType().getArity();
  if (arity >= 64 || length(getTable().getType()) != (uint64_t(1) << arity))
    return refuse(*this, "MLE table length must equal two to the result arity");
  return success();
}
LogicalResult AddPolynomialOp::verify() { return binary(*this); }
LogicalResult MultiplyPolynomialOp::verify() { return binary(*this); }
LogicalResult FixPolynomialOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  if (getPrefix().size() > getInput().getType().getArity() ||
      getPolynomial().getType().getArity() !=
          getInput().getType().getArity() - getPrefix().size())
    return refuse(*this, "fix removes exactly the ordered prefix axes");
  return success();
}
LogicalResult SumPolynomialOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  auto count = getCountAttr().getInt();
  if (count < 0 || uint64_t(count) > getInput().getType().getArity() ||
      getPolynomial().getType().getArity() !=
          getInput().getType().getArity() - uint64_t(count))
    return refuse(*this, "sum removes exactly the ordered Boolean suffix axes");
  return success();
}
LogicalResult EvaluatePolynomialOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  if (getPoint().size() != getPolynomial().getType().getArity())
    return refuse(*this, "evaluation point must match the polynomial arity");
  return success();
}
LogicalResult PolynomialCoefficientsOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  if (getPolynomial().getType().getArity() != 1)
    return refuse(*this, "coefficient observation is univariate");
  return success();
}
LogicalResult EvaluateDomainOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  if (getPolynomial().getType().getArity() != 1 ||
      getPoints().size() != length(getValues().getType()))
    return refuse(
        *this,
        "domain evaluation requires a univariate and exact result length");
  return verifyDomain(*this, field(getValues().getType()).getDomain(),
                      getPoints());
}
LogicalResult InterpolateDomainOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  if (getPolynomial().getType().getArity() != 1 ||
      getPoints().size() != length(getValues().getType()))
    return refuse(
        *this,
        "interpolation requires exact domain length and univariate result");
  return verifyDomain(*this, field(getValues().getType()).getDomain(),
                      getPoints());
}
LogicalResult FixTableOp::verify() {
  if (failed(sameField(*this)))
    return failure();
  uint64_t input = length(getTable().getType());
  if (!isPowerOf2_64(input) || getPrefix().size() >= 64 ||
      (uint64_t(1) << getPrefix().size()) > input ||
      length(getResult().getType()) != (input >> getPrefix().size()))
    return refuse(*this, "table fixing removes an in-bounds high-bit prefix");
  return success();
}

LogicalResult deriveDegrees(Block &body, Degrees &result) {
  result.bounds.clear();
  unsigned remaining = 100000;
  for (auto &operation : body) {
    Operation *op = &operation;
    if (!remaining--)
      return refuse(op,
                    "polynomial degree analysis exceeds its operation budget");
    if (auto observed = dyn_cast<PolynomialCoefficientsOp>(op)) {
      auto bound = result.bounds.find(observed.getPolynomial());
      if (bound == result.bounds.end() || bound->second.size() != 1 ||
          bound->second[0] >= length(observed.getCoefficients().getType()))
        return refuse(
            op, "coefficient length requires a known fitting degree bound");
    }
    if (op->getNumResults() != 1 ||
        !isa<PolynomialType>(op->getResult(0).getType()))
      continue;
    SmallVector<uint64_t> degrees;
    auto type = cast<PolynomialType>(op->getResult(0).getType());
    if (isa<ConstantPolynomialOp>(op))
      degrees.assign(type.getArity(), 0);
    else if (isa<MultilinearPolynomialOp>(op))
      degrees.assign(type.getArity(), 1);
    else if (isa<CoefficientPolynomialOp, InterpolateDomainOp>(op))
      degrees.push_back(length(op->getOperand(0).getType()) - 1);
    else if (isa<AddPolynomialOp, MultiplyPolynomialOp>(op)) {
      auto left = result.bounds.find(op->getOperand(0));
      auto right = result.bounds.find(op->getOperand(1));
      if (left == result.bounds.end() || right == result.bounds.end())
        continue;
      if (left->second.size() != right->second.size())
        return refuse(op, "degree arity mismatch");
      for (auto [a, b] : zip(left->second, right->second)) {
        if (isa<MultiplyPolynomialOp>(op) &&
            a > std::numeric_limits<uint64_t>::max() - b)
          return refuse(op, "degree bound overflow");
        degrees.push_back(isa<MultiplyPolynomialOp>(op) ? a + b
                                                        : std::max(a, b));
      }
    } else if (isa<FixPolynomialOp, SumPolynomialOp>(op)) {
      auto input = result.bounds.find(op->getOperand(0));
      if (input == result.bounds.end())
        continue;
      auto values = ArrayRef<uint64_t>(input->second);
      if (auto fix = dyn_cast<FixPolynomialOp>(op))
        values = values.drop_front(fix.getPrefix().size());
      else
        values = values.take_front(type.getArity());
      degrees.assign(values.begin(), values.end());
    } else
      continue;
    if (degrees.size() != type.getArity())
      return refuse(op, "degree arity mismatch");
    result.bounds[op->getResult(0)] = std::move(degrees);
  }
  return success();
}

void eraseUnusedPolynomials(Block &body, Degrees &degrees) {
  for (auto &op : llvm::make_early_inc_range(llvm::reverse(body))) {
    if (op.getNumResults() != 1 || !op.use_empty())
      continue;
    if (!isa<ConstantPolynomialOp, CoefficientPolynomialOp,
             MultilinearPolynomialOp, AddPolynomialOp, MultiplyPolynomialOp,
             FixPolynomialOp, SumPolynomialOp, InterpolateDomainOp,
             EvaluatePolynomialOp, PolynomialCoefficientsOp, EvaluateDomainOp,
             FixTableOp>(op))
      continue;
    degrees.bounds.erase(op.getResult(0));
    op.erase();
  }
}

#define POLYNOMIAL_MEANING(OP, ID)                                             \
  std::optional<MathematicalIdentity> OP::getMathematicalIdentity() {          \
    return MathematicalIdentity::ID;                                           \
  }                                                                            \
  SmallVector<unsigned> OP::getOperandDependencies(unsigned result) {          \
    return allOperands(*this, result);                                         \
  }
POLYNOMIAL_MEANING(ConstantPolynomialOp, PolynomialConstant)
POLYNOMIAL_MEANING(CoefficientPolynomialOp, PolynomialFromCoefficients)
POLYNOMIAL_MEANING(MultilinearPolynomialOp, PolynomialMLE)
POLYNOMIAL_MEANING(AddPolynomialOp, PolynomialAdd)
POLYNOMIAL_MEANING(MultiplyPolynomialOp, PolynomialMultiply)
POLYNOMIAL_MEANING(FixPolynomialOp, PolynomialFix)
POLYNOMIAL_MEANING(SumPolynomialOp, PolynomialSum)
POLYNOMIAL_MEANING(EvaluatePolynomialOp, PolynomialEvaluate)
POLYNOMIAL_MEANING(PolynomialCoefficientsOp, PolynomialCoefficients)
POLYNOMIAL_MEANING(EvaluateDomainOp, PolynomialEvaluateDomain)
POLYNOMIAL_MEANING(InterpolateDomainOp, PolynomialInterpolate)
POLYNOMIAL_MEANING(FixTableOp, PolynomialFixTable)
#undef POLYNOMIAL_MEANING
} // namespace zkc::poly
