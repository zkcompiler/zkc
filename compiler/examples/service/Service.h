#ifndef ZKC_EXAMPLES_SERVICE_H
#define ZKC_EXAMPLES_SERVICE_H
#include "zkc/Dialect/IR.h"

#include "ServiceDialect.h.inc"
#define GET_TYPEDEF_CLASSES
#include "ServiceTypes.h.inc"
#define GET_OP_CLASSES
#include "ServiceOps.h.inc"
namespace zkc::service {
void registerService(mlir::DialectRegistry &registry, bool ambiguous = false);
}
#endif
