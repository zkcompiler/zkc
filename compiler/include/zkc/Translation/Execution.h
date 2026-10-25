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
} // namespace zkc::protocol
#endif
