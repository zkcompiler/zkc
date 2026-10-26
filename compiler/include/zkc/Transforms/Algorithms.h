#ifndef ZKC_TRANSFORMS_ALGORITHMS_H
#define ZKC_TRANSFORMS_ALGORITHMS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/Support/Error.h"
#include <memory>

namespace zkc::mathematical {
struct RealizationTrace;
}
namespace zkc::protocol {
struct AlgorithmOrigin;
/// Expand ordinary scoped helper calls by checked SSA substitution, retaining
/// typed mathematical/finite requests and explicit scope/outcome control.
/// Source and candidate are separate owned modules. The independent checker
/// reads both actual CFGs; no native model or Local IR is produced as a
/// rewrite. Source returns remain uncharged. This is not native artifact
/// admission. Optional occurrence paths are recovered by the independent
/// checker and published only after complete success; a refusal leaves the
/// output intact.
mlir::OwningOpRef<mlir::ModuleOp>
expandScopedHelpers(mlir::ModuleOp source,
                    std::vector<AlgorithmOrigin> *origins = nullptr);
mlir::LogicalResult verifyScopedHelperExpansionPreserved(
    mlir::ModuleOp source, mlir::ModuleOp candidate,
    std::vector<AlgorithmOrigin> *origins = nullptr);
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
mlir::LogicalResult
expandAlgorithms(mlir::ModuleOp, std::vector<AlgorithmOrigin> * = nullptr,
                 mathematical::RealizationTrace *trace = nullptr);
/// RetainMaps expands bodies that transitively call admitted map/finite
/// declarations and callbacks named by finite declarations, retaining only
/// preparation calls. Other declarations and call-free callbacks stay exact.
/// Finish expands remaining calls and forbids preparation declarations.
/// Both phases share substitution, source-inspection, depth and origin limits
/// through state. Each is transactional and independently checked by virtual
/// source substitution or exact unchanged-body correspondence.
mlir::LogicalResult
expandAlgorithms(mlir::ModuleOp, AlgorithmExpansionPhase,
                 AlgorithmExpansionState &,
                 std::vector<AlgorithmOrigin> * = nullptr,
                 mathematical::RealizationTrace *trace = nullptr);
mlir::LogicalResult verifyStagedAlgorithmExpansionPreserved(
    mlir::ModuleOp before, mlir::ModuleOp after, AlgorithmExpansionPhase,
    const AlgorithmExpansionState &beforeState,
    const AlgorithmExpansionState &afterState);
} // namespace zkc::protocol
#endif
