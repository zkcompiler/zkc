#ifndef ZKC_DIALECT_REGISTRY_H
#define ZKC_DIALECT_REGISTRY_H
#include "llvm/Support/Error.h"
namespace mlir {
class DialectRegistry;
class MLIRContext;
} // namespace mlir
namespace zkc {
enum class InvocationPrecondition {
  LoadedProtocolDialects,
  LoadedTableDialect
};
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

/// Register protocol, mathematical and executable dialects, standard func/arith
/// and mathematical interface models, plus installed contributions.
/// The finite-table dialect and source library models are excluded.
void registerNativeDialects(mlir::DialectRegistry &registry);
/// Register all built-in dialects; source library models remain opt-in.
void registerDialects(mlir::DialectRegistry &registry);
/// Test the protocol import precondition (independent of Table and arith)
/// without loading dialects or changing the
/// context.
bool hasProtocolDialects(mlir::MLIRContext &context);
} // namespace zkc
#endif
