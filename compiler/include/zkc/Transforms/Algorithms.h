#ifndef ZKC_TRANSFORMS_ALGORITHMS_H
#define ZKC_TRANSFORMS_ALGORITHMS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/Support/Error.h"

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
/// Drop scoped helper definitions unreachable from the complete participant
/// declaration context. Every non-scoped declaration is a root, including
/// projection metadata. Both modules are admitted; retained declarations are
/// compared independently and must be unchanged and in their original order.
/// This operation is restricted to the participant profile: role-free function
/// exports are not subject to participant reachability.
mlir::OwningOpRef<mlir::ModuleOp>
pruneParticipantHelpers(mlir::ModuleOp source);
mlir::LogicalResult
verifyParticipantHelperPruningPreserved(mlir::ModuleOp source,
                                        mlir::ModuleOp candidate);
/// One retained primitive occurrence after scoped expansion. Path consists of
/// (call site, callee) pairs, relative to the enclosing invocation.
struct AlgorithmOrigin {
  std::string function, site, definition, originalSite;
  protocol::Assignments path;
};
/// Canonical encoding of an expanded occurrence. Long encodings use a digest;
/// full paths remain in AlgorithmOrigin. Charge bytes before constructing it.
llvm::Expected<std::string> algorithmSite(const protocol::Assignments &path,
                                          llvm::StringRef site,
                                          uint64_t &remainingBytes);
} // namespace zkc::protocol
#endif
