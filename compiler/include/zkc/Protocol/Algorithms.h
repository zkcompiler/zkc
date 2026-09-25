#ifndef ZKC_PROTOCOL_ALGORITHMS_H
#define ZKC_PROTOCOL_ALGORITHMS_H

#include "zkc/Protocol/Module.h"

namespace zkc::protocol {
/// One retained primitive occurrence after local expansion. Path consists of
/// (call site, callee) pairs, relative to the enclosing local invocation.
struct AlgorithmOrigin {
  std::string function, site, definition, originalSite;
  source::Assignments path;
};
/// Canonical encoding of a local occurrence. Bounded by source site limits.
llvm::Expected<std::string> algorithmSite(const source::Assignments &path,
                                          llvm::StringRef site);
/// Transactional, order-preserving expansion on actual SSA and symbol calls.
/// Common IR may retain func.call; participant/physical export may not.
mlir::LogicalResult expandAlgorithms(mlir::ModuleOp,
                                     std::vector<AlgorithmOrigin> * = nullptr);
struct ExpandedAlgorithms {
  source::Module source;
  std::vector<AlgorithmOrigin> origins;
};
llvm::Expected<ExpandedAlgorithms> expandAlgorithms(const source::Module &,
                                                    mlir::MLIRContext &);
} // namespace zkc::protocol
#endif
