#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLATTRS_H
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLATTRS_H

#include "mlir/IR/Attributes.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Dialect/Protocol/IR/protocolEnums.h.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolAttrs.h.inc"

namespace zkc::protocol_ir {
bool isMathematicalProfile(Profile profile);
bool isExecutableProfile(Profile profile);
// Services are features of these explicit contracts, never a stage inference.
bool isProgram(ExecutionContract contract);
} // namespace zkc::protocol_ir

#endif
