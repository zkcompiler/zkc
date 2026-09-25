#ifndef ZKC_COMPILER_DIAGNOSTICS_H
#define ZKC_COMPILER_DIAGNOSTICS_H
#include "zkc/Dialect/Diagnostics.h"
namespace zkc {
struct DiagnosticLocation {
  std::string filename;
  unsigned line, column;
};
/// Owned rendering and structured refusal metadata survive context teardown.
/// An upstream diagnostic may have no zkc refusal identifier.
class CompilationError : public llvm::ErrorInfo<CompilationError> {
public:
  static char ID;
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  /// Recognized file locations in diagnostic order; upstream locations without
  /// file coordinates remain available in the owned rendering.
  std::vector<DiagnosticLocation> locations;
  CompilationError(std::string message,
                   std::vector<diagnostics::RefusalInfo> refusals,
                   std::vector<DiagnosticLocation> locations = {})
      : message(std::move(message)), refusals(std::move(refusals)),
        locations(std::move(locations)) {}
  void log(llvm::raw_ostream &out) const override { out << message; }
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
};
} // namespace zkc
#endif
