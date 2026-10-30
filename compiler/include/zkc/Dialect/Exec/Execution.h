#ifndef ZKC_DIALECT_EXEC_EXECUTION_H
#define ZKC_DIALECT_EXEC_EXECUTION_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
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
/// Admit the current scoped source closure before mathematical realization.
/// In addition to ordinary helpers, permits typed exec.compute and ordered
/// exec.fold/collect with supported native logical ports, after checking actual
/// mathematical bodies, domains, callbacks and call premises. Reuses logical
/// affine/resource admission over actual native SSA, closed control captures
/// and finite callback edges. No declaration is admitted from a synthetic
/// mathematical signature.
/// Checks every immediate scoped/math definition and selected computation unit,
/// including dormant ones. Other declarations belong to the enclosing profile.
/// Ordered affine fold state additionally requires preservation of each exact
/// state root on every continuing callback path, using the admitted control
/// view and operation successor contracts.
/// This does not establish source correspondence or permit unresolved calls in
/// an executable artifact.
llvm::Error verifySourceExecutionClosure(mlir::Operation *symbolTable);
/// Transient admitted native view for analyses. All data/control associations
/// refer to actual immutable IR. Unresolved requests retain actual operations,
/// not synthetic signatures, executable declarations or mathematical proofs.
struct SourceExecutionStep {
  mlir::Operation *operation = nullptr;
  llvm::SmallVector<mlir::Value> inputs, outputs;
  llvm::SmallVector<mlir::func::FuncOp> regions;
  bool conditional = false;
};
struct SourceExecutionClosure {
  /// Actual unresolved computation occurrences. These references borrow the
  /// immutable source IR and supply association, not mathematical evidence.
  /// Private byte-format declaration names belong only to the exporter.
  llvm::SmallVector<mlir::Operation *> computations;
  /// Structured association recovered while checking the actual CFG. Values
  /// are the original SSA values, including distinct closed-region formals
  /// even when their actual captures alias. Administrative scope/outcome edges
  /// are consumed by the reader, not silently skipped by downstream clients.
  /// Like computations, this view borrows the immutable source IR.
  std::map<std::string, std::vector<SourceExecutionStep>> bodies;
};
llvm::Expected<SourceExecutionClosure>
readSourceExecutionClosure(mlir::Operation *symbolTable);
/// Read a closed transient numerical schedule directly, including scoped SCF
/// loops. This entrypoint does not widen source or native executable admission.
/// Every declaration must be a runtime binding or scoped function; unresolved
/// helpers, computations and other declarations are refused. The returned
/// records/SSA association are derived from the actual immutable schedule.
llvm::Expected<SourceExecutionClosure>
readScheduledExecutionClosure(mlir::Operation *symbolTable);
/// Read the fully realized native profile with its actual SSA/control
/// association. No ordinary helper or mathematical requests are admitted.
llvm::Expected<SourceExecutionClosure>
readExecutionClosure(mlir::Operation *symbolTable, bool physical);
} // namespace zkc::protocol
#endif
