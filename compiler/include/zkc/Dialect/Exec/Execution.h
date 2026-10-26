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
/// also admits every immediate plain mathematical function and its domain
/// closure through the mathematical owner. The returned view contains only
/// scoped definitions; it does not describe mathematical equations or admit
/// mathematical/finite realization requests. It is not language-source
/// correspondence, and its result cannot be published unexpanded.
llvm::Expected<program::LocalDefinitions>
readSourceExecutionDefinitions(mlir::Operation *symbolTable);
/// Admit the current scoped source closure before mathematical realization.
/// In addition to ordinary helpers, permits typed exec.compute and ordered
/// exec.fold/collect with supported native logical ports, after checking actual
/// mathematical bodies, domains, callbacks and call premises. Reuses logical
/// affine/resource admission with transient derived signatures and actual
/// finite callback edges; no model or source declaration is returned.
/// Checks every immediate scoped/math definition and selected computation unit,
/// including dormant ones. Other declarations belong to the enclosing profile.
/// Ordered affine fold state additionally requires preservation of each exact
/// state root on every continuing callback path, using the admitted control
/// view and operation successor contracts.
/// This does not establish source correspondence or permit unresolved calls in
/// an executable artifact.
llvm::Error verifySourceExecutionClosure(mlir::Operation *symbolTable);
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
/// Recheck plain mathematical admission too; correspondence of those equations
/// to their source remains the language/mathematical checker's responsibility.
llvm::Error
verifySourceExecutionDefinitions(mlir::Operation *symbolTable,
                                 const program::LocalDefinitions &expected);
} // namespace zkc::protocol
#endif
