#ifndef ZKC_LANGUAGE_ORACLEINSPECTION_H
#define ZKC_LANGUAGE_ORACLEINSPECTION_H
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
namespace zkc::language::detail {
llvm::json::Object describeOracleDefinition(llvm::ArrayRef<Declaration>,
                                            const Declaration &);
} // namespace zkc::language::detail
#endif
