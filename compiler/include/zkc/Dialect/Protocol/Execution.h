#ifndef ZKC_DIALECT_PROTOCOL_EXECUTION_H
#define ZKC_DIALECT_PROTOCOL_EXECUTION_H
#include "zkc/Program/Model.h"
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
/// Residual computation units and exec.compute/fold/collect calls must first be
/// realized. Native profile admission checks their actual definitions and SSA
/// directly; it does not call this byte-model reconstruction adapter.
llvm::Expected<program::Participants> readExecutionModel(mlir::Operation *);
} // namespace zkc::protocol
#endif
