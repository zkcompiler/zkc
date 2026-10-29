#ifndef ZKC_COMPILER_ORACLEOBLIGATIONS_H
#define ZKC_COMPILER_ORACLEOBLIGATIONS_H
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <string>
namespace mlir {
class MLIRContext;
}
namespace zkc::protocol {
/// Derive condition templates and ordered virtual footprints from the verified
/// original structured source. These proposals do not prove their obligations.
llvm::Expected<std::string> exportOracleObligations(llvm::StringRef original,
                                                    llvm::StringRef symbol,
                                                    mlir::MLIRContext &);
/// Compare the exact complete proposal with a fresh derivation from the
/// original. The independent Lean consumer owns a separate implementation of
/// this check.
llvm::Error checkOracleObligations(llvm::StringRef original,
                                   llvm::StringRef symbol,
                                   llvm::StringRef proposal,
                                   mlir::MLIRContext &);
} // namespace zkc::protocol
#endif
