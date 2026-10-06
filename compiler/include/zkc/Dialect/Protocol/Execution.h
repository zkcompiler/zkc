#ifndef ZKC_DIALECT_PROTOCOL_EXECUTION_H
#define ZKC_DIALECT_PROTOCOL_EXECUTION_H
#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
namespace mlir {
class Operation;
}
namespace zkc::protocol {
/// Check local IR invariants, reconstruct the ordered execution model and admit
/// its executable grammar. Module-level projection metadata and native profile
/// policy are separate checks run by mlir::verify; this reader does not call
/// them recursively. It neither serializes a carrier nor proves source
/// correspondence. Native logical models are valid here before selection.
llvm::Expected<source::Content> readExecutionModel(mlir::Operation *);
} // namespace zkc::protocol
#endif
