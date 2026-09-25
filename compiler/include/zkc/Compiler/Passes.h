#ifndef ZKC_COMPILER_PASSES_H
#define ZKC_COMPILER_PASSES_H
namespace zkc {
/// Register built-in passes. Tools opt into registration; linking the library
/// does not mutate MLIR's global pass registry.
void registerCompilerPasses();
} // namespace zkc
#endif
