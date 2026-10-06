#ifndef ZKC_TRANSFORMS_PROTOCOL_APPLICATIONS_H
#define ZKC_TRANSFORMS_PROTOCOL_APPLICATIONS_H
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
namespace zkc::mathematical {
// Mutates only an owned, admitted candidate. Callers discard it on failure.
mlir::LogicalResult expandApplications(protocol_ir::ProtocolModuleOp);
} // namespace zkc::mathematical
#endif
