#ifndef ZKC_FRONTEND_LIBRARY_DIAGNOSTIC_H
#define ZKC_FRONTEND_LIBRARY_DIAGNOSTIC_H

#include "zkc/Frontend/Library.h"

namespace zkc::frontend::library {
/// The library checker owns these fields. Consumers must not recover an
/// obligation or checker identity by interpreting the rendered message.
class Diagnostic : public llvm::ErrorInfo<Diagnostic> {
public:
  static char ID;
  std::string code, message;
  std::optional<Requirement> obligation;
  std::string checker;

  Diagnostic(std::string code, std::string message,
             std::optional<Requirement> obligation = {},
             std::string checker = {})
      : code(std::move(code)), message(std::move(message)),
        obligation(std::move(obligation)), checker(std::move(checker)) {}
  void log(llvm::raw_ostream &out) const override {
    out << code << ": " << message;
  }
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
};
} // namespace zkc::frontend::library
#endif
