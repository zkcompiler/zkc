#ifndef ZKC_DRIVER_COMPILER_H
#define ZKC_DRIVER_COMPILER_H
#include "mlir/IR/DialectRegistry.h"
namespace zkc {
int runCompiler(int argc, char **argv, const mlir::DialectRegistry &registry);
} // namespace zkc
#endif
