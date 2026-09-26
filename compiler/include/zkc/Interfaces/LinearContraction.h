#ifndef ZKC_INTERFACES_LINEAR_CONTRACTION_H
#define ZKC_INTERFACES_LINEAR_CONTRACTION_H
#include "mlir/IR/OpDefinition.h"
#include <optional>

namespace zkc {
/// Optional semantic roles for a pointwise scalar action and a linear
/// contraction. These describe the logical scalar-action equation, not an
/// installed representation, implementation, purity, or buffer aliasing.
/// Target selection must independently admit the complete installed contract
/// and cover every result use at a compatible values operand in the same block.
struct DiagonalProducerRoles {
  unsigned factorsOperand, valuesOperand, result;
};
struct DiagonalContractionRoles {
  unsigned coefficientsOperand, valuesOperand;
};
} // namespace zkc
#include "zkc/Interfaces/LinearContraction.h.inc"
#endif
