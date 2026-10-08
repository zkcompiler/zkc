#ifndef ZKC_TRANSLATION_PROTOCOL_H
#define ZKC_TRANSLATION_PROTOCOL_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Program/Model.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/JSON.h"
#include <string>
#include <vector>

namespace zkc::protocol {
/// Decode actual native program bytes and independently compare their
/// executable view to physical SSA, including local bodies, bindings, services
/// and entries. Allows SSA renaming. Locations, projection/relation
/// declarations, implicit immutable capture forwarding and argument display
/// names are not serialized. Returns the admitted, compared program.
llvm::Expected<program::Participants>
verifyProgramArtifact(mlir::Operation *subject, llvm::StringRef bytes);
/// Reconstruct and admit the complete root, including generated relations.
/// This is checked export; local operation invariants alone are insufficient.
llvm::Expected<program::Participants> exportProgram(mlir::Operation *);
llvm::Expected<llvm::json::Value> exportModule(mlir::Operation *);
} // namespace zkc::protocol
#endif
