#ifndef ZKC_TRANSFORMS_MATHEMATICALTRACE_H
#define ZKC_TRANSFORMS_MATHEMATICALTRACE_H

#include "zkc/Support/OptimizationOutcome.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalWork.h"
#include <cstdint>
#include <string>
#include <variant>
#include <vector>

namespace llvm {
class raw_ostream;
}
namespace zkc::mathematical {
/// Owned identity in the immutable stage input. Paths distinguish repeated
/// helper calls. Generated subjects are qualified by the event's service and
/// parent proposal; identity is not promised across arbitrary source edits.
struct RealizationSubject {
  std::string declaration, site, operation;
  std::vector<unsigned> position;
  std::string definition, originalSite;
  std::vector<std::pair<std::string, std::string>> occurrence;
  bool operator==(const RealizationSubject &other) const {
    return declaration == other.declaration && site == other.site &&
           operation == other.operation && position == other.position &&
           definition == other.definition &&
           originalSite == other.originalSite && occurrence == other.occurrence;
  }
};
enum class DecisionFamily {
  Finite,
  NestedContraction,
  Lanes,
  Map,
  MapProduct,
  VectorReduction
};
enum class RealizationChoice {
  Ordered,
  Bilinear,
  Reduction,
  Elementwise,
  NestedContraction,
  MapProduct,
  MapSum
};
enum class PublicationBoundary {
  IncorporatedIntoParent,
  ReturnedCandidate,
  PublishedToCaller
};
enum class CompletionKind { Completed, Unchanged, Refused };
enum class VerificationObservation {
  Verified,
  Mismatch,
  OptionalCapacity,
  RequiredCapacity,
  Refused
};
/// Verification remains distinct from optional recognition. The reader owns
/// this cause, including any subject or debit precision it actually exposes.
struct VerificationDecision {
  VerificationObservation outcome = VerificationObservation::Mismatch;
  std::string detail;
  std::optional<CapacityCause> capacity = {};
  RealizationSubject subject = {};
};
struct RequiredFailure {
  std::string detail;
  std::optional<CapacityCause> capacity = {};
};
using DecisionCause =
    std::variant<OptimizationOutcome, VerificationDecision, RequiredFailure>;
struct SelectionDecision {
  DecisionFamily family;
  RealizationChoice choice;
  OptimizationOutcome outcome;
  RealizationSubject querySubject;
};
struct ProposalDecision {
  MathematicalSelectionPolicy effectivePolicy;
};
struct DiscardDecision {
  DecisionCause cause;
};
struct RetryDecision {
  uint64_t discardedProposal;
  MathematicalSelectionPolicy effectivePolicy;
};
struct PublicationDecision {
  PublicationBoundary boundary;
};
struct CompletionDecision {
  CompletionKind outcome;
  std::optional<DecisionCause> cause = {};
};
using RealizationEventPayload =
    std::variant<SelectionDecision, ProposalDecision, DiscardDecision,
                 RetryDecision, PublicationDecision, CompletionDecision>;
struct RealizationEvent {
  uint64_t sequence, scope, parent;
  std::string service;
  RealizationSubject subject = {};
  RealizationEventPayload payload;
};
/// Diagnostic measurements, never admission evidence or final publication.
struct RealizationStage {
  std::string name;
  bool completed = false;
  uint64_t operationsBefore = 0, operationsAfter = 0;
  uint64_t microseconds = 0;
};
struct RealizationTrace {
  /// Original request. Effective policy belongs to each proposal/retry.
  MathematicalSelectionPolicy policy;
  std::vector<RealizationStage> stages;
  std::vector<RealizationEvent> events;
  RealizationWork initialWork, remainingWork;
  bool remarks = false;
  /// Caller-owned diagnostic stream, live throughout the synchronous call.
  llvm::raw_ostream *ir = nullptr;

  /// Internal synchronous scope bookkeeping, separate from copied work. Only
  /// entry with no active scope clears a reused trace. Events own no IR refs.
  std::vector<uint64_t> activeScopes;
  uint64_t nextScope = 1;
};
} // namespace zkc::mathematical
#endif
