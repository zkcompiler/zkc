#ifndef ZKC_TRANSLATION_EXECUTION_H
#define ZKC_TRANSLATION_EXECUTION_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Reconstruct native local definitions from the bounded Func/CF execution
/// profile. Read actual bodies, scopes, bindings and outcome edges; refuse
/// unconsumed blocks and unchecked callees. The returned model is independently
/// admitted. This is not source correspondence or physical artifact comparison.
llvm::Expected<program::LocalDefinitions>
readLocalExecution(mlir::ModuleOp module, bool physical);
/// Emit the canonical scoped Func/CF profile from independently admitted native
/// definitions. Value-type dialects must already be loaded. Generated structure
/// is verified; source and artifact correspondence remain separate obligations.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
writeLocalExecution(mlir::MLIRContext &context,
                    const program::LocalDefinitions &definitions,
                    bool physical);
/// Independently compare current actual CFG with admitted native definitions.
/// Allows SSA renaming; checks all actual bodies and bindings without calling
/// the reconstruction reader or replaying emission. No source theorem is
/// implied.
llvm::Error verifyLocalExecution(mlir::ModuleOp module,
                                 const program::LocalDefinitions &expected,
                                 bool physical);
} // namespace zkc::protocol
#endif
