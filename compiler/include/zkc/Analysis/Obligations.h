#ifndef ZKC_ANALYSIS_OBLIGATIONS_H
#define ZKC_ANALYSIS_OBLIGATIONS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <vector>

namespace zkc::analysis {

/// An index into a caller-owned table of exact, interpreted propositions.
/// The caller establishes relation/operand/context identity before indexing.
using ClaimId = uint32_t;

/// If every premise holds, the conclusion holds under the admitted rule's law
/// and exceptional-event assumptions. This record does not establish that law.
struct ReductionRule {
  std::vector<ClaimId> premises;
  ClaimId conclusion;
};

/// Each step indexes the separately admitted rule table. A candidate cannot
/// supply a new rule through this certificate. Requirements, facts, and rule
/// validity must come from the caller's independently checked source/execution
/// contracts, not from the candidate certificate itself.
using ObligationCertificate = std::vector<uint32_t>;

/// Check an ordered derivation and coverage of all original requirements.
/// Facts are reusable; a repeated requirement cannot hide another requirement.
/// Missing premises and forward references refuse instead of being assumed.
/// Resource limits cover both the rule table and expanded certificate work.
/// This verifies logical closure, not terminal truth, body correspondence,
/// cryptographic soundness, probability bounds, or resource linearity.
llvm::Error checkObligations(uint32_t claimCount,
                             llvm::ArrayRef<ClaimId> required,
                             llvm::ArrayRef<ClaimId> facts,
                             llvm::ArrayRef<ReductionRule> rules,
                             llvm::ArrayRef<uint32_t> certificate);

/// Derive a deterministic certificate by forward chaining admitted rules.
/// Unseeded cycles produce no facts. The worklist visits each rule and premise
/// occurrence at most once; the resulting certificate is independently checked
/// by checkObligations. This does not remove any runtime verifier operations.
llvm::Expected<ObligationCertificate>
deriveObligations(uint32_t claimCount, llvm::ArrayRef<ClaimId> required,
                  llvm::ArrayRef<ClaimId> facts,
                  llvm::ArrayRef<ReductionRule> rules);

} // namespace zkc::analysis

#endif
