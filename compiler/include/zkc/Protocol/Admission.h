#ifndef ZKC_PROTOCOL_ADMISSION_H
#define ZKC_PROTOCOL_ADMISSION_H

#include "zkc/Source/Model.h"
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
/// Ordinary source admission never enables native literals in common modules.
llvm::Error
admitNativeLocalDefinitions(const source::Module &,
                            llvm::ArrayRef<LocalRealization> realizations = {});
/// Formation and executable admission are distinct. On failure, optionally
/// identify a record borrowed from the immutable input for diagnostics.
/// This source interface does not require an MLIR context.
llvm::Error admit(const source::Content &, bool executable,
                  const source::Node **failureLocation = nullptr);
llvm::Error admit(const source::Module &, bool executable,
                  const source::Node **failureLocation = nullptr);
llvm::Error admit(const source::Participants &, bool executable,
                  const source::Node **failureLocation = nullptr);
} // namespace zkc::protocol

#endif
