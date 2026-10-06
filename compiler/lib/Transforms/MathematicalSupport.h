#ifndef ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#define ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#include "zkc/Dialect/Operations.h"
namespace zkc::mathematical {
// Internal rewrite entry used by preparation and participant simplification.
// The caller has already admitted the complete unit.
mlir::LogicalResult simplifyCalculations(mlir::Operation *body);
// Build retained obligations from the original common definition.
mlir::ArrayAttr statementBindings(protocol_ir::MathematicalOp program,
                                  mlir::SymbolTableCollection &symbols);
// Both complete modules have passed ordinary verification, including the
// module-owned calculation-attribution check.
mlir::LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                       protocol_ir::ProtocolModuleOp candidate);
} // namespace zkc::mathematical
#endif
