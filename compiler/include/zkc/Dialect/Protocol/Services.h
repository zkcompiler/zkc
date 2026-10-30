#ifndef ZKC_DIALECT_PROTOCOL_SERVICES_H
#define ZKC_DIALECT_PROTOCOL_SERVICES_H
#include "mlir/IR/TypeRange.h"
#include "zkc/Contracts/Services.h"
namespace zkc::protocol_ir {
/// Compare actual logical ports to an installed service declaration through
/// native catalog observations. No type codec, representation selection,
/// authority check or sampling algorithm is implied by this signature check.
bool matchesServiceSignature(mlir::TypeRange inputs, mlir::TypeRange outputs,
                             const protocol::ServiceMethod &method);
} // namespace zkc::protocol_ir
#endif
