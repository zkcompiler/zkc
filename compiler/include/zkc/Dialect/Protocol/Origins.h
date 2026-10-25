#ifndef ZKC_DIALECT_PROTOCOL_ORIGINS_H
#define ZKC_DIALECT_PROTOCOL_ORIGINS_H
#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/Support/JSON.h"

namespace zkc::protocol_ir {
/// Translate the checked public tree without stringifying nested terms.
mlir::ArrayAttr protocolOriginAttr(mlir::MLIRContext *,
                                   const llvm::json::Value &);
/// Bounded, strict decoding; this checks syntax, not source/body
/// correspondence.
llvm::Expected<llvm::json::Value> readProtocolOrigin(mlir::Attribute);
} // namespace zkc::protocol_ir
#endif
