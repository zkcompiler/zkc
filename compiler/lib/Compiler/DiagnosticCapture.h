#ifndef ZKC_COMPILER_DIAGNOSTICCAPTURE_H
#define ZKC_COMPILER_DIAGNOSTICCAPTURE_H
#include "zkc/Compiler/Diagnostics.h"
#include <optional>
namespace zkc::detail {
llvm::Error compilationError(llvm::Error);
/// Invocation-owned capture for a complete MLIR context, including pass worker
/// threads. Do not install competing invocation collectors on the same context.
/// The returned error owns every field and survives destruction of the context.
class DiagnosticCapture {
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  std::vector<InvocationPrecondition> preconditions;
  std::optional<mlir::Location> root;
  bool sawError = false;
  mlir::ScopedDiagnosticHandler handler;

public:
  explicit DiagnosticCapture(mlir::MLIRContext &context);
  void atRoot(mlir::Location location) { root = location; }
  bool hasErrors() const { return sawError; }
  llvm::Error failure(llvm::Error fallback = llvm::Error::success());
};
} // namespace zkc::detail
#endif
