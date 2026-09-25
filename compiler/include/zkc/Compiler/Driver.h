#ifndef ZKC_COMPILER_DRIVER_H
#define ZKC_COMPILER_DRIVER_H
#include "mlir/IR/DialectRegistry.h"
namespace zkc {
int runCompiler(int argc, char **argv, const mlir::DialectRegistry &registry);
} // namespace zkc
#endif
