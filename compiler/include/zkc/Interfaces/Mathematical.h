#ifndef ZKC_INTERFACES_MATHEMATICAL_H
#define ZKC_INTERFACES_MATHEMATICAL_H

#include "mlir/IR/OpDefinition.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>

namespace mlir {
class DialectRegistry;
}
namespace zkc {
enum class MathematicalIdentity {
  FieldAdd,
  FieldMultiply,
  FieldEqual,
  GroupAdd,
  GroupScale,
  GroupEqual,
  Pairing,
  BooleanConstant,
  BooleanAnd,
  BooleanOr,
  BooleanXor,
  BooleanEqual,
  BooleanNotEqual,
  Select,
  FieldConstant,
  FieldSubtract,
  ArrayFromElements,
  ArrayAt,
  PolynomialConstant,
  PolynomialFromCoefficients,
  PolynomialMLE,
  PolynomialAdd,
  PolynomialMultiply,
  PolynomialFix,
  PolynomialSum,
  PolynomialEvaluate,
  PolynomialCoefficients,
  PolynomialEvaluateDomain,
  PolynomialInterpolate,
  PolynomialFixTable
};

/// Register external models for the narrow upstream Boolean vocabulary.
/// An interface describes an operation; closed profile admission independently
/// checks its exact registered identity, attributes, types and context.
void registerMathematicalInterfaces(mlir::DialectRegistry &registry);
} // namespace zkc

#include "zkc/Interfaces/Mathematical.h.inc"
#endif
