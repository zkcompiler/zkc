#ifndef ZKC_DIALECT_RELATION_IR_DECLARATIONS_H
#define ZKC_DIALECT_RELATION_IR_DECLARATIONS_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/ArrayRef.h"

namespace zkc::relation {
// Validate the actual union selected by a compilation or linker. Names are
// local lookup identities; equal external identities must agree on schema.
// No process-global registry and no claim about the external predicate's truth.
mlir::LogicalResult
verifyDeclarationConsistency(llvm::ArrayRef<mlir::Operation *> units);
} // namespace zkc::relation

#endif
