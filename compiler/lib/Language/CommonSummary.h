#ifndef ZKC_LANGUAGE_COMMONSUMMARY_H
#define ZKC_LANGUAGE_COMMONSUMMARY_H

#include "zkc/Language/CommonControl.h"

namespace zkc::language::detail {
struct Work;
/// Invocation-local diagnostics, never an admission premise or persistent key.
/// Counts include work preceding refusal. Each reader supplies its own owner.
struct CommonSummaryObservation {
  uint64_t templates = 0, instances = 0, instanceHits = 0;
  uint64_t applications = 0, applicationHits = 0, expressions = 0;
  uint64_t bodyTraversals = 0, loopNamespaces = 0;
};
llvm::Expected<std::vector<CommonControlRequirement>>
deriveCommonSummaryRequirements(const std::vector<Declaration> &,
                                llvm::ArrayRef<Asset>, Work &, DeclarationId,
                                CommonSummaryObservation &);
llvm::Error checkCommonSummaryRequirements(const std::vector<Declaration> &,
                                           llvm::ArrayRef<Asset>, Work &,
                                           CommonSummaryObservation &);
} // namespace zkc::language::detail
#endif
