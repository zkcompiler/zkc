//===- LinkEngine.h - route-preserving protocol composition ----*- C++ -*-===//
#ifndef ZKC_SEMANTICS_LINKENGINE_H
#define ZKC_SEMANTICS_LINKENGINE_H

#include "mlir/Support/LogicalResult.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ProtocolEnvironment.h"

#include <utility>

namespace zkc::semantics {

/// Static composition for the currently represented fresh/local-challenge
/// protocol carrier. The input protocols remain intact on every outcome.
class LinkEngine {
public:
  explicit LinkEngine(registry::ProtocolEnvironment environment)
      : environment_(std::move(environment)) {}

  /// Judge both faces, splice them under disjoint namespaces, re-author their
  /// construction routes, and judge the resulting open protocol. Failure
  /// leaves no partial composite in the IR.
  mlir::FailureOr<pir::ProtocolOp> link(pir::ProtocolOp producer,
                                        pir::ProtocolOp consumer,
                                        llvm::StringRef producerPrefix,
                                        llvm::StringRef consumerPrefix) const;

private:
  registry::ProtocolEnvironment environment_;
};

} // namespace zkc::semantics

#endif // ZKC_SEMANTICS_LINKENGINE_H
