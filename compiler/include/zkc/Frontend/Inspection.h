#ifndef ZKC_FRONTEND_INSPECTION_H
#define ZKC_FRONTEND_INSPECTION_H

#include "zkc/Frontend/Analysis.h"
#include "llvm/Support/JSON.h"

namespace zkc::frontend {
/// Diagnostic view of a source snapshot, including incomplete input. This is
/// neither a PIR carrier nor a certificate of source or protocol correctness.
llvm::json::Value inspectAnalysis(const Analysis &);
} // namespace zkc::frontend

#endif
