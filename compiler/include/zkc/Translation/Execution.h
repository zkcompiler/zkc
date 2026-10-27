#ifndef ZKC_TRANSLATION_EXECUTION_H
#define ZKC_TRANSLATION_EXECUTION_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Emit the canonical scoped Func/CF profile from independently admitted native
/// definitions. Value-type dialects must already be loaded. Generated structure
/// is verified; source and artifact correspondence remain separate obligations.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
writeLocalExecution(mlir::MLIRContext &context,
                    const program::LocalDefinitions &definitions,
                    bool physical);
} // namespace zkc::protocol
#endif
