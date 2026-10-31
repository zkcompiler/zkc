#ifndef ZKC_LANGUAGE_ORACLEINSPECTION_H
#define ZKC_LANGUAGE_ORACLEINSPECTION_H
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
namespace zkc::language::detail {
struct Work;
/// Whole-predicate lookup addresses, separate from construction occurrences.
llvm::Expected<llvm::json::Object>
oracleAdmissibilityCompanions(llvm::ArrayRef<Declaration>, const Declaration &,
                              Work &);
llvm::Expected<llvm::json::Object>
describeOracleDefinition(llvm::ArrayRef<Declaration>, const Declaration &,
                         Work &);
} // namespace zkc::language::detail
#endif
