#ifndef ZKC_DRIVER_COMPILER_H
#define ZKC_DRIVER_COMPILER_H
#include "mlir/IR/DialectRegistry.h"
namespace zkc {
/// Runs a CLI invocation with built-in dialects plus caller-supplied
/// extensions. An empty registry is valid; source library models remain opt-in.
int runCompiler(int argc, char **argv, const mlir::DialectRegistry &registry);
} // namespace zkc
#endif
