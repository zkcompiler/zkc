#ifndef ZKC_PROTOCOL_ADMISSION_H
#define ZKC_PROTOCOL_ADMISSION_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
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
