#ifndef ZKC_CLAIMS_ANALYSIS_H
#define ZKC_CLAIMS_ANALYSIS_H
#include "zkc/Analysis/Obligations.h"
#include "zkc/Claims/Claims.h"
#include "zkc/Source/Execution.h"
#include <map>
namespace zkc::claims {
/// Derived source-relative analysis, not caller authority or a security proof.
inline constexpr size_t maxRecords = 32768;
inline constexpr size_t maxItems = 200000;
struct Trace : source::Execution {
  std::string digest;
};
struct Checked {
  Trace source;
  std::string contractDigest;
  std::map<std::string, uint32_t> claimIds, ruleIds;
  std::vector<uint32_t> required, facts;
  std::vector<analysis::ReductionRule> rules;
};
llvm::Expected<Checked> admit(const source::Module &, const Contract &);
llvm::Expected<std::vector<uint32_t>> steps(const Checked &,
                                            const Certificate &);
} // namespace zkc::claims
#endif
