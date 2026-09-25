#ifndef ZKC_CLAIMS_DRIVER_H
#define ZKC_CLAIMS_DRIVER_H
#include "mlir/IR/DialectRegistry.h"
namespace zkc::claims {
int runCommand(int argc, char **argv, const mlir::DialectRegistry &);
}
#endif
