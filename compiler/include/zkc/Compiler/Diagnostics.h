#ifndef ZKC_COMPILER_DIAGNOSTICS_H
#define ZKC_COMPILER_DIAGNOSTICS_H
#include "zkc/Dialect/Diagnostics.h"
namespace zkc {
/// Owned rendering and structured refusal metadata survive context teardown.
/// An upstream diagnostic may have no zkc refusal identifier.
class CompilationError : public llvm::ErrorInfo<CompilationError> {
public:
  static char ID;
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  CompilationError(std::string message,
                   std::vector<diagnostics::RefusalInfo> refusals)
      : message(std::move(message)), refusals(std::move(refusals)) {}
  void log(llvm::raw_ostream &out) const override { out << message; }
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
};
} // namespace zkc
#endif
