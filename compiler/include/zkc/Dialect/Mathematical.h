#ifndef ZKC_DIALECT_MATHEMATICAL_H
#define ZKC_DIALECT_MATHEMATICAL_H
#include "zkc/Dialect/Operations.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Twine.h"

namespace zkc::mathematical {
// A static application occurrence prefixes the callee's site. Source-origin
// capture and actual expansion must use the same injective spelling.
inline std::string expandedApplicationSite(llvm::StringRef caller,
                                           llvm::StringRef callee) {
  return (llvm::Twine("apply_") + llvm::Twine(caller.size()) + "_" + caller +
          "_" + callee)
      .str();
}
// Transient analysis of the current IR. Never a serialized authority or a
// second expression representation; recompute after changing that IR.
struct Availability {
  llvm::DenseMap<mlir::Value, llvm::BitVector> values;
};
// Requires a stable containing module that has passed formation verification,
// including every callee repeat invariant. Caches expire with this invocation.
// Single-program query with local analysis budgets. Use verifyModule for
// aggregate admission; callers must not infer a module work bound from queries.
mlir::LogicalResult analyze(zkc::protocol_ir::MathematicalOp program,
                            Availability &result,
                            mlir::SymbolTableCollection &tables);
mlir::LogicalResult verifyModule(protocol_ir::ProtocolModuleOp module);
mlir::LogicalResult
verifyParticipantModule(protocol_ir::ProtocolModuleOp module);
mlir::LogicalResult
verifyProjectionMetadata(protocol_ir::ProtocolModuleOp module);
bool isTotal(mlir::Operation *operation);
// Validate acyclic static applications and their total expansion budget.
mlir::LogicalResult verifyApplications(protocol_ir::ProtocolModuleOp module);
} // namespace zkc::mathematical
#endif
