#ifndef ZKC_INTERFACES_LINEAR_CONTRACTION_H
#define ZKC_INTERFACES_LINEAR_CONTRACTION_H
#include "mlir/IR/OpDefinition.h"
#include <optional>
#include <string>

namespace zkc {
/// Optional physical choices for a depth-one diagonal map and a contraction.
/// These describe operand roles, not purity, buffer aliasing, or a checked law.
/// A producer advertises an immutable view with dense factors/backing.
/// Selection must cover every result use at a compatible contraction values
/// operand in the same block; this is not an affine-resource consumption
/// interface.
struct DiagonalProducerSelection {
  unsigned factorsOperand, valuesOperand, result;
  std::string representation, implementation;
};
struct DiagonalContractionSelection {
  unsigned coefficientsOperand, valuesOperand;
  std::string representation, implementation;
};
} // namespace zkc
#include "zkc/Interfaces/LinearContraction.h.inc"
#endif
