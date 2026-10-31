#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLTYPES_H
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLTYPES_H
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Dialect/Protocol/IR/ProtocolAttrs.h"
#include "zkc/Dialect/Protocol/IR/ProtocolDialect.h"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolTypes.h.inc"

namespace zkc::protocol_ir {
// Shape observations for the closed handle/sequence family. These do not
// establish custody, availability or admission; other types return null.
OracleKindAttr getOracleFamilyKind(mlir::Type type);
mlir::Type getOracleFamilyDataType(mlir::Type type);
} // namespace zkc::protocol_ir

#endif
