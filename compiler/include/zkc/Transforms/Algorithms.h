#ifndef ZKC_TRANSFORMS_ALGORITHMS_H
#define ZKC_TRANSFORMS_ALGORITHMS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
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
} // namespace zkc::protocol
#endif
