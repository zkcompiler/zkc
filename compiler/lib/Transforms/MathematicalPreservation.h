#ifndef ZKC_TRANSFORMS_MATHEMATICALPRESERVATION_H
#define ZKC_TRANSFORMS_MATHEMATICALPRESERVATION_H
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
namespace zkc::mathematical {
// Build retained obligations from the original common definition. Each names
// its relation declaration; identity, signature and purposes stay there.
mlir::ArrayAttr statementBindings(protocol_ir::MathematicalOp program);
// Both complete modules have passed ordinary verification, including the
// module-owned calculation-attribution check.
// `batching` selects the calculation schedule the candidate must have.
mlir::LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                       protocol_ir::ProtocolModuleOp candidate,
                                       bool batching = true);
} // namespace zkc::mathematical
#endif
