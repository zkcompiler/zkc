#ifndef ZKC_DIALECT_BINDINGTYPECACHE_H
#define ZKC_DIALECT_BINDINGTYPECACHE_H
namespace mlir {
class DialectRegistry;
}
namespace zkc::protocol {
// Register a bounded, context-owned memo for immutable native type translation.
// It changes neither the installed contract set nor operation admission.
void registerBindingTypeCache(mlir::DialectRegistry &);
} // namespace zkc::protocol
#endif
