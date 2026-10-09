#ifndef ZKC_INTERFACES_MATHEMATICAL_H
#define ZKC_INTERFACES_MATHEMATICAL_H

#include "mlir/IR/OpDefinition.h"
#include "zkc/Contracts/Mathematical.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>

namespace mlir {
class DialectRegistry;
}
namespace zkc {
/// Register external models for the narrow upstream Boolean vocabulary.
/// An interface describes an operation; closed profile admission independently
/// checks its exact registered identity, attributes, types and context.
void registerMathematicalInterfaces(mlir::DialectRegistry &registry);
} // namespace zkc

#include "zkc/Interfaces/Mathematical.h.inc"
#endif
