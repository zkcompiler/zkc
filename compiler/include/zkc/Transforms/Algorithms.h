#ifndef ZKC_TRANSFORMS_ALGORITHMS_H
#define ZKC_TRANSFORMS_ALGORITHMS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/Support/Error.h"
#include <memory>

namespace zkc::protocol {
namespace detail {
struct AlgorithmExpansionRecord;
struct AlgorithmStateAccess;
} // namespace detail
enum class AlgorithmExpansionPhase { RetainMaps, Finish };
/// Transient, compiler-owned occurrence paths and cumulative preparation
/// budgets. Copying retains an immutable snapshot. Use the state returned by
/// RetainMaps for checked vector rewrites and Finish on that same subject.
/// It is not serialized IR or a claim of admission for arbitrary edited IR.
class AlgorithmExpansionState {
  std::shared_ptr<const detail::AlgorithmExpansionRecord> record;
  friend struct detail::AlgorithmStateAccess;
};
/// One retained primitive occurrence after local expansion. Path consists of
/// (call site, callee) pairs, relative to the enclosing local invocation.
struct AlgorithmOrigin {
  std::string function, site, definition, originalSite;
  protocol::Assignments path;
};
/// Canonical encoding of a local occurrence. Long encodings use a digest;
/// full paths remain in AlgorithmOrigin. Charge bytes before constructing it.
llvm::Expected<std::string> algorithmSite(const protocol::Assignments &path,
                                          llvm::StringRef site,
                                          uint64_t &remainingBytes);
/// Independently compare actual local expansion by virtual source substitution.
/// Refuses unrecognized rewrites and bounds work; does not emit a candidate.
mlir::LogicalResult verifyAlgorithmExpansionPreserved(mlir::ModuleOp before,
                                                      mlir::ModuleOp after);
/// Transactional, order-preserving expansion on actual SSA and symbol calls.
/// Common IR may retain local.apply; participant/physical export may not.
mlir::LogicalResult expandAlgorithms(mlir::ModuleOp,
                                     std::vector<AlgorithmOrigin> * = nullptr);
/// RetainMaps expands ordinary helpers, retaining only admitted map calls.
/// Finish expands the realized remainder and forbids preparation declarations.
/// Both phases share work, depth and origin limits through state. Each is
/// transactional and independently checked by virtual source substitution.
mlir::LogicalResult expandAlgorithms(mlir::ModuleOp, AlgorithmExpansionPhase,
                                     AlgorithmExpansionState &,
                                     std::vector<AlgorithmOrigin> * = nullptr);
mlir::LogicalResult verifyStagedAlgorithmExpansionPreserved(
    mlir::ModuleOp before, mlir::ModuleOp after, AlgorithmExpansionPhase,
    const AlgorithmExpansionState &beforeState,
    const AlgorithmExpansionState &afterState);
} // namespace zkc::protocol
#endif
