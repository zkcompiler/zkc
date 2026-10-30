#ifndef ZKC_PROGRAM_ADMISSION_H
#define ZKC_PROGRAM_ADMISSION_H

#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Independently check neutral logical source definitions for export and
/// comparison. Ordinary LocalApply edges must resolve to actual function bodies
/// in this model. Native closure admission uses the actual IR directly.
llvm::Error admitNativeLocalDefinitions(const program::LocalDefinitions &);
/// Admit an execution definition subset, including an empty one, without
/// inventing a participant entry. Physical ports and bindings are checked when
/// selected. Unresolved mathematical calls are not permitted.
llvm::Error admitExecutionDefinitions(const program::LocalDefinitions &,
                                      bool physical = false);
/// Check executable formation and local definitions.
/// The model interface does not require an MLIR context.
llvm::Error admit(const program::Participants &);
} // namespace zkc::protocol

#endif
