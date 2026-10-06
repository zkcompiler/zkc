#ifndef ZKC_DIALECT_PROTOCOL_SEMANTICS_H
#define ZKC_DIALECT_PROTOCOL_SEMANTICS_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>

namespace zkc::mathematical {
// Applications are total helper calls whose per-result meaning comes from a
// checked definition. Primitive expressions have their own operation interface.
enum class Category { Total, Application, Action, Control, Declaration };
enum Context : unsigned { Protocol = 1, Participant = 2, Helper = 4 };
struct OperationSemantics {
  Category category;
  unsigned contexts;
};
// Exact registered operation identity, never purity or interface presence.
std::optional<OperationSemantics> classify(mlir::Operation *operation);
// Shared by availability, helper summaries and projection. The current scalar
// vocabulary requires each primitive result to depend on every operand. A
// future subset-dependent primitive also needs a reviewed projection
// representation.
mlir::FailureOr<llvm::SmallVector<unsigned>>
operandDependencies(mlir::Operation *operation, unsigned result);
// Check the exact inherent attribute vocabulary too. Arbitrary discardable
// attributes cannot grant assumptions or new semantic options in this profile.
mlir::LogicalResult verifyOperation(mlir::Operation *operation,
                                    Context context);
} // namespace zkc::mathematical

#endif
