#ifndef ZKC_COMPILER_CLAIMS_H
#define ZKC_COMPILER_CLAIMS_H
#include "zkc/Claims/Claims.h"
#include "zkc/Protocol/PhysicalOptions.h"
namespace mlir {
class MLIRContext;
}
namespace zkc::claims {
/// Context registration is an invocation responsibility; load required dialects
/// before checking. Missing built-ins refuse without loading more dialects.
/// These APIs never change the supplied registry.
/// Same original source is mandatory at both independent checking boundaries.
llvm::Error checkConstruction(const source::Module &, const Contract &,
                              const Certificate &, const source::Construction &,
                              const llvm::json::Value &, mlir::MLIRContext &);
/// Re-run existing construction, projection and physical lowering, then compare
/// the actual exported candidate. The bounded API supports the existing
/// physical transformations and explicit implementation selections. A selection
/// snapshot refers to the checked constructed protocol.
llvm::Error checkLowering(const source::Module &, const Contract &,
                          const Certificate &, const source::Construction &,
                          const llvm::json::Value &construction,
                          const llvm::json::Value &physical,
                          mlir::MLIRContext &,
                          const protocol::PhysicalOptions &options = {});
} // namespace zkc::claims
#endif
