#ifndef ZKC_PROGRAM_ADMISSION_H
#define ZKC_PROGRAM_ADMISSION_H

#include "zkc/Program/Model.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Signature supplied only by an admitted mathematical module. This is not a
/// source-carrier declaration or permission to export an unresolved call.
struct LocalRealization {
  std::string name;
  std::vector<std::string> inputs, outputs;
};
/// Internal logical native locals, without any protocol or entry declarations.
/// Realization signatures are permitted only for local.apply checking.
llvm::Error
admitNativeLocalDefinitions(const program::LocalDefinitions &,
                            llvm::ArrayRef<LocalRealization> realizations = {});
/// Check executable formation and local definitions.
/// The model interface does not require an MLIR context.
llvm::Error admit(const program::Participants &);
} // namespace zkc::protocol

#endif
