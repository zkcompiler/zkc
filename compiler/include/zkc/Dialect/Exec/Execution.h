#ifndef ZKC_DIALECT_EXEC_EXECUTION_H
#define ZKC_DIALECT_EXEC_EXECUTION_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Program/Admission.h"
#include "llvm/Support/Error.h"
#include <map>

namespace zkc::protocol {
/// Select the execution checking owner from the signature or execution
/// markers, including malformed partial signatures. This is not admission.
bool isScopedExecutionFunction(mlir::func::FuncOp function);
/// Logical data signature of an ordinary scoped helper: exclude its borrowed
/// scope and expose the outcome payload. Returns null for malformed signatures
/// and outlined control bodies. This is shape inspection, not body admission.
mlir::FunctionType scopedDataSignature(mlir::func::FuncOp function);
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
/// Transient admitted logical view for analyses before realization. Computation
/// signatures are derived from the actual checked definitions and retain finite
/// callback edges. They are not executable declarations or mathematical
/// equations. Consumers must not publish this view as an executable program.
struct SourceExecutionStep {
  mlir::Operation *operation = nullptr;
  llvm::SmallVector<mlir::Value> inputs, outputs;
  llvm::SmallVector<mlir::func::FuncOp> regions;
  bool conditional = false;
};
struct SourceExecutionClosure {
  program::LocalDefinitions definitions;
  std::vector<LocalRealization> computations;
  /// Actual occurrences from which private computation signatures were read.
  /// These references borrow the immutable source IR; a changed body or source
  /// invalidates the view. They supply association, not mathematical evidence.
  std::map<std::string, mlir::Operation *> computationOrigins;
  /// Structured association recovered while checking the actual CFG. Values
  /// are the original SSA values, including distinct closed-region formals
  /// even when their actual captures alias. Administrative scope/outcome edges
  /// are consumed by the reader, not silently skipped by downstream clients.
  /// Like computationOrigins, this view borrows the immutable source IR.
  std::map<std::string, std::vector<SourceExecutionStep>> bodies;
};
llvm::Expected<SourceExecutionClosure>
readSourceExecutionClosure(mlir::Operation *symbolTable);
/// Read the fully realized native profile with its actual SSA/control
/// association. No ordinary helper or mathematical requests are admitted.
llvm::Expected<SourceExecutionClosure>
readExecutionClosure(mlir::Operation *symbolTable, bool physical);
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
