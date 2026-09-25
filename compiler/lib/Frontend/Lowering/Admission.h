#ifndef ZKC_FRONTEND_LOWERING_ADMISSION_H
#define ZKC_FRONTEND_LOWERING_ADMISSION_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::frontend {
llvm::Error checkSourceContent(const source::Content &,
                               const source::Node **failureLocation = nullptr);
} // namespace zkc::frontend
#endif
