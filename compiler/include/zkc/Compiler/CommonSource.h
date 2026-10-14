#ifndef ZKC_COMPILER_COMMONSOURCE_H
#define ZKC_COMPILER_COMMONSOURCE_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/JSON.h"

namespace zkc::protocol {
/// Export an admitted common protocol or private pure relation function to the
/// bounded scalar Lean source carrier. Checks the whole original before
/// traversing actual operands; expands only pure helpers, without
/// simplification. Unsupported operations refuse. The digest identifies
/// supplied original bytes, not a formal proof of the exporter, native
/// projection, runtime, or cryptographic interpretation.
llvm::Expected<llvm::json::Value>
exportCommonSource(llvm::StringRef originalBytes, llvm::StringRef symbol,
                   mlir::MLIRContext &context);
} // namespace zkc::protocol
#endif
