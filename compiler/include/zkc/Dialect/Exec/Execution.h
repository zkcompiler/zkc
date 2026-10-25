#ifndef ZKC_DIALECT_EXEC_EXECUTION_H
#define ZKC_DIALECT_EXEC_EXECUTION_H

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
/// Read every immediate Runtime binding and Func definition in one symbol
/// table. Other declarations remain the enclosing profile's responsibility;
/// no immediate Func can be omitted from the selected table. Checks actual
/// owned operations without recursively invoking the enclosing profile's
/// verifier.
llvm::Expected<program::LocalDefinitions>
readExecutionDefinitions(mlir::Operation *symbolTable, bool physical);
/// Read logical scoped definitions before ordinary helper expansion. Direct
/// func.call edges borrow the current scope, retain runtime.site and expose
/// their exact outcome. Root functions package returns without a native tick;
/// outlined control bodies still perform charged native yield. Checks every
/// actual helper body and admits the complete acyclic closure. This component
/// does not admit mathematical/finite realization requests or prove language
/// source correspondence, and its result cannot be published unexpanded.
llvm::Expected<program::LocalDefinitions>
readSourceExecutionDefinitions(mlir::Operation *symbolTable);
/// Independently compare current actual CFG with admitted native definitions.
/// Allows SSA renaming; checks all actual bodies and bindings without calling
/// the reconstruction reader or replaying emission. No source theorem is
/// implied.
llvm::Error verifyLocalExecution(mlir::ModuleOp module,
                                 const program::LocalDefinitions &expected,
                                 bool physical);
/// Independently compare every immediate binding and Func definition in a
/// mixed symbol table. This checks the complete scoped-function inventory,
/// not the other declarations, enclosing stage or protocol associations.
llvm::Error
verifyExecutionDefinitions(mlir::Operation *symbolTable,
                           const program::LocalDefinitions &expected,
                           bool physical);
/// Independently compare the same logical source-scoped profile, including
/// actual helper targets, occurrences, ports and every dormant definition.
llvm::Error
verifySourceExecutionDefinitions(mlir::Operation *symbolTable,
                                 const program::LocalDefinitions &expected);
} // namespace zkc::protocol
#endif
