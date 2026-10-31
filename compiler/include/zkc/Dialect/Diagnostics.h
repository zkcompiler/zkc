#ifndef ZKC_DIALECT_DIAGNOSTICS_H
#define ZKC_DIALECT_DIAGNOSTICS_H

#include "mlir/IR/Diagnostics.h"
#include "llvm/Support/Error.h"
#include <string>
#include <thread>
#include <utility>
#include <vector>

namespace zkc::diagnostics {
/// Capture or observe diagnostics from a synchronous service on this thread.
/// MLIR handlers belong to the context: sibling invocations can emit while
/// this scope is active, even at the same location. Forward their diagnostics
/// without calling the service's handler or touching its invocation state.
/// Nested scopes retain MLIR's usual last-registered-first dispatch. This is
/// not a collector for work delegated to other threads; such work needs its
/// own scopes, or a caller-owned collector for the complete execution context.
class ScopedThreadDiagnosticHandler {
  mlir::ScopedDiagnosticHandler handler;

public:
  template <typename Handler>
  ScopedThreadDiagnosticHandler(mlir::MLIRContext *context, Handler &&callback)
      : handler(context, [thread = std::this_thread::get_id(),
                          callback = std::forward<Handler>(callback)](
                             mlir::Diagnostic &diagnostic) mutable {
          if (std::this_thread::get_id() != thread)
            return mlir::failure();
          return callback(diagnostic);
        }) {}
  ScopedThreadDiagnosticHandler(const ScopedThreadDiagnosticHandler &) = delete;
  ScopedThreadDiagnosticHandler &
  operator=(const ScopedThreadDiagnosticHandler &) = delete;
};

struct RefusalInfo {
  std::string code;
  /// Complete owned detail supplied at emission.
  std::string detail;
};

/// Attach owned, nonprinting metadata and render the refusal on the existing
/// diagnostic. Its location, severity, operation prefix and notes are retained.
/// Form the complete detail before calling: subsequently streamed text does
/// not update metadata. Attach related context as notes on the returned value.
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
