#ifndef ZKC_DIALECT_REGISTRY_H
#define ZKC_DIALECT_REGISTRY_H
namespace mlir {
class DialectRegistry;
}
namespace zkc {
/// Register the built-in dialects; source library models remain opt-in.
void registerDialects(mlir::DialectRegistry &registry);
} // namespace zkc
#endif
