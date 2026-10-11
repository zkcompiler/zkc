#ifndef ZKC_TRANSFORMS_MATHEMATICALCOMPARISON_H
#define ZKC_TRANSFORMS_MATHEMATICALCOMPARISON_H

#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/ValueRange.h"
#include "zkc/Analysis/Finite.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::mathematical {
/// Compare a closed scalar formula with actual scalar/lane instructions after
/// the caller has checked all ordered input length guards. Every source and
/// candidate payload operation, including unused operations, must belong to
/// the admitted total fragment. Inputs correspond to source block arguments;
/// rowwise inputs have the common length witnessed by rows. No terminator is
/// read. On success cursor follows the consumed payload and the returned SSA
/// value denotes the formula vector. The caller must check its actual use and
/// preserve the unchanged suffix. Cursor and bindings are unchanged on failure.
mlir::FailureOr<mlir::Value> compareLaneFormula(
    mlir::Block &source, llvm::ArrayRef<bool> rowwise, mlir::ValueRange inputs,
    mlir::Value rows, mlir::Operation *&cursor, mlir::SymbolTable &symbols,
    llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining);

/// Compare the sum of a mapped scalar formula with actual candidate payload
/// operations (for example a dot product). The ordered length guards and
/// unchanged surrounding context have the same obligations as above.
mlir::FailureOr<mlir::Value> compareLaneSum(
    mlir::Block &source, llvm::ArrayRef<bool> rowwise, mlir::ValueRange inputs,
    mlir::Value rows, mlir::Operation *&cursor, mlir::SymbolTable &symbols,
    llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining);

/// Independently interpret a finite source domain/helper and actual candidate
/// payload. `inputs` maps the finite signature to candidate SSA; `rows` is the
/// root cardinality already read by the ordered admission checker. No selector,
/// emitter plan, or producer access map is accepted. Unsupported ordered
/// computations return failure so the caller can use its ordered loop reader.
mlir::FailureOr<mlir::Value> compareFinitePayload(
    const finite::Computation &source, mlir::ValueRange inputs,
    mlir::Value rows, mlir::Operation *&cursor, mlir::SymbolTable &symbols,
    llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining);
} // namespace zkc::mathematical
#endif
