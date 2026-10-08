#ifndef ZKC_DIALECT_REGISTRY_H
#define ZKC_DIALECT_REGISTRY_H
#include "llvm/Support/Error.h"
namespace mlir {
class DialectRegistry;
class MLIRContext;
} // namespace mlir
namespace zkc {
enum class InvocationPrecondition { LoadedProtocolDialects };
/// An embedding configuration failure, not a semantic source refusal.
class DialectRegistrationError
    : public llvm::ErrorInfo<DialectRegistrationError> {
public:
  static char ID;
  InvocationPrecondition precondition;
  std::string detail;
  DialectRegistrationError(InvocationPrecondition precondition,
                           std::string detail)
      : precondition(precondition), detail(std::move(detail)) {}
  void log(llvm::raw_ostream &out) const override { out << detail; }
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
};

/// Register all native mathematical and execution dialects and interfaces.
void registerDialects(mlir::DialectRegistry &registry);
/// Test the native dialect registration precondition
/// without loading dialects or changing the
/// context.
bool hasProtocolDialects(mlir::MLIRContext &context);
} // namespace zkc
#endif
