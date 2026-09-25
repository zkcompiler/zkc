#ifndef ZKC_LLZK_ADAPTER_H
#define ZKC_LLZK_ADAPTER_H

#include <cstddef>
namespace mlir {
class ModuleOp;
}
namespace zkc::llzk_adapter {
int run(int argc, char **argv);
// Final admission boundary, separately exercised against a faulty normalizer.
// Throws a stable refusal diagnostic; returns the scalar equality count.
size_t validateScalarModule(mlir::ModuleOp module);
} // namespace zkc::llzk_adapter
#endif
