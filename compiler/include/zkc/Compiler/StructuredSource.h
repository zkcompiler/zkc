#ifndef ZKC_COMPILER_STRUCTUREDSOURCE_H
#define ZKC_COMPILER_STRUCTUREDSOURCE_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/JSON.h"

namespace zkc::protocol {
/// Verify the whole supplied original, then export the bounded, single-role
/// structured profile without preparation, projection or helper expansion.
/// The digest binds the supplied bytes; it is not a correspondence proof.
llvm::Expected<llvm::json::Value>
exportStructuredSource(llvm::StringRef originalBytes, llvm::StringRef symbol,
                       mlir::MLIRContext &context);
} // namespace zkc::protocol
#endif
