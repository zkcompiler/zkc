#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLATTRS_H
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLATTRS_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Dialect/Protocol/IR/protocolEnums.h.inc"
#include <optional>
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolAttrs.h.inc"

namespace zkc::protocol_ir {
bool isMathematicalProfile(Profile profile);
bool isExecutableProfile(Profile profile);
// Services are features of these explicit contracts, never a stage inference.
} // namespace zkc::protocol_ir

#endif
