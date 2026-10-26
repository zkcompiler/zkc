#ifndef ZKC_TRANSFORMS_MATHEMATICALCOMPARISON_H
#define ZKC_TRANSFORMS_MATHEMATICALCOMPARISON_H

#include "zkc/Support/OptimizationOutcome.h"

#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/ValueRange.h"
#include "zkc/Analysis/Finite.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::mathematical {
class ScopedCandidate;
/// Limits of the independent interpreter, not evidence of inequivalence.
enum class ComparisonCapacity {
  None,
  Work,
  Inputs,
  Nodes,
  Depth,
  Outputs,
  Encoding,
  Multiplicity,
  HelperDepth,
  DomainDepth
};
llvm::StringRef comparisonCapacityName(ComparisonCapacity capacity);
/// Compare a closed scalar formula with actual scalar/lane instructions after
/// the caller has checked all ordered input length guards. Every source and
/// candidate payload operation, including unused operations, must belong to
/// the admitted total fragment. Inputs correspond to source block arguments;
/// rowwise inputs have the common length witnessed by rows. No terminator is
/// read. If end is supplied, every instruction up to that exclusive boundary
/// is admitted, including unused instructions. Otherwise reading stops as soon
/// as a result matches, leaving the entire suffix to the caller.
/// On success cursor follows the consumed payload and the returned SSA
/// value denotes the formula vector. The caller must check its actual use and
/// preserve the unchanged suffix. Cursor and bindings are unchanged on failure.
/// If supplied, capacity is reset on entry and distinguishes interpreter
/// exhaustion from a mismatch. An exact allowance may be consumed on success.
/// An engaged output names the actual result. An engaged empty Value permits
/// any matching result inside the complete span; the caller checks its use.
/// Without output, a supplied end must be the single-output terminator.
mlir::FailureOr<mlir::Value> compareLaneFormula(
    mlir::Block &source, llvm::ArrayRef<bool> rowwise, mlir::ValueRange inputs,
    mlir::Value rows, mlir::Operation *&cursor, mlir::SymbolTable &symbols,
    llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining,
    mlir::Operation *end = nullptr, ComparisonCapacity *capacity = nullptr,
    std::optional<CapacityCause> *debit = nullptr,
    std::optional<mlir::Value> output = std::nullopt,
    const ScopedCandidate *candidate = nullptr);

/// Compare the sum of a mapped scalar formula with actual candidate payload
/// operations (for example a dot product). The ordered length guards and
/// unchanged surrounding context have the same obligations as above.
mlir::FailureOr<mlir::Value> compareLaneSum(
    mlir::Block &source, llvm::ArrayRef<bool> rowwise, mlir::ValueRange inputs,
    mlir::Value rows, mlir::Operation *&cursor, mlir::SymbolTable &symbols,
    llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining,
    mlir::Operation *end = nullptr, ComparisonCapacity *capacity = nullptr,
    std::optional<CapacityCause> *debit = nullptr,
    std::optional<mlir::Value> output = std::nullopt,
    const ScopedCandidate *candidate = nullptr);

/// Independently interpret a finite source domain/helper and actual candidate
/// payload. `inputs` maps the finite signature to candidate SSA; `rows` is the
/// root cardinality already read by the ordered admission checker. No selector,
/// emitter plan, or producer access map is accepted. Unsupported ordered
/// computations return failure so the caller can use its ordered loop reader.
/// If supplied, capacity is reset on entry and names an exhausted interpreter
/// limit on failure. A successful comparison may consume exactly its allowance.
/// Cursor and bindings are published only on success.
mlir::FailureOr<mlir::Value> compareFinitePayload(
    const finite::Computation &source, mlir::ValueRange inputs,
    mlir::Value rows, mlir::Operation *&cursor, mlir::SymbolTable &symbols,
    llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining,
    mlir::Operation *end = nullptr, ComparisonCapacity *capacity = nullptr,
    std::optional<CapacityCause> *debit = nullptr,
    const ScopedCandidate *candidate = nullptr);

/// Cheap candidate-side gate for the optional finite semantic comparison.
/// Ordered recipes begin with index constants or empty containers and must
/// not pay to interpret the source helper before entering their own reader.
bool hasFinitePayloadContract(mlir::Operation *cursor,
                              mlir::SymbolTable &symbols);
} // namespace zkc::mathematical
#endif
