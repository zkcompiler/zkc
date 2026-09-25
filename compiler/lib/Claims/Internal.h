#ifndef ZKC_CLAIMS_INTERNAL_H
#define ZKC_CLAIMS_INTERNAL_H
#include "zkc/Claims/Analysis.h"
namespace zkc::claims {
llvm::Expected<Trace> trace(const source::Module &, llvm::StringRef entry);
std::string digest(llvm::StringRef domain, const llvm::json::Value &);
} // namespace zkc::claims
#endif
