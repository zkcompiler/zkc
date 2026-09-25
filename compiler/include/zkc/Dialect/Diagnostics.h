#ifndef ZKC_DIALECT_DIAGNOSTICS_H
#define ZKC_DIALECT_DIAGNOSTICS_H

#include "mlir/IR/Diagnostics.h"
#include "llvm/Support/Error.h"
#include <string>
#include <vector>

namespace zkc::diagnostics {
struct RefusalInfo {
  std::string code;
  /// Detail supplied at emission; later streamed context stays in MLIR's text.
  std::string detail;
};

/// Attach owned, nonprinting metadata and render the refusal on the existing
/// diagnostic. Its location, severity, operation prefix and notes are retained.
mlir::InFlightDiagnostic emit(mlir::InFlightDiagnostic diagnostic,
                              llvm::StringRef code,
                              const llvm::Twine &detail = {});
/// Transport every native Refusal in an LLVM error, preserving LLVM's rendering
/// and order. Foreign errors retain their text and receive no invented code.
mlir::InFlightDiagnostic emit(mlir::InFlightDiagnostic diagnostic,
                              llvm::Error error);
/// Copy refusal metadata without parsing diagnostic prose. Empty for ordinary
/// MLIR/LLVM diagnostics. Notes have their own metadata and are not flattened.
std::vector<RefusalInfo> refusals(mlir::Diagnostic &diagnostic);
} // namespace zkc::diagnostics
#endif
