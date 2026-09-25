#ifndef ZKC_DIALECT_REGISTRY_H
#define ZKC_DIALECT_REGISTRY_H
namespace mlir {
class DialectRegistry;
class MLIRContext;
} // namespace mlir
namespace zkc {
/// Register the built-in dialects; source library models remain opt-in.
void registerDialects(mlir::DialectRegistry &registry);
/// Test the import precondition without loading dialects or changing the
/// context.
bool hasProtocolDialects(mlir::MLIRContext &context);
} // namespace zkc
#endif
