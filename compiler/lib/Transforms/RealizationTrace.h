#ifndef ZKC_TRANSFORMS_REALIZATIONTRACE_H
#define ZKC_TRANSFORMS_REALIZATIONTRACE_H

#include "AlgorithmSupport.h"
#include "FiniteVerification.h"
#include "RealizationSubject.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/Support/raw_ostream.h"
#include <type_traits>

namespace zkc::mathematical {
inline RealizationSubject
realizationSubject(mlir::Operation *op,
                   const protocol::detail::AlgorithmExpansionRecord &record) {
  auto result = realizationSubject(op);
  if (auto *origin = protocol::detail::occurrence(record, result.declaration,
                                                  result.site)) {
    result.definition = origin->definition;
    result.originalSite = origin->originalSite;
    result.occurrence.assign(origin->path.begin(), origin->path.end());
  }
  return result;
}

inline RealizationSubject
realizationSubject(const finite::ComputationDiagnostic &diagnostic) {
  auto key = realizationSubject(diagnostic.subject);
  for (auto *op : diagnostic.occurrencePath) {
    auto occurrence = realizationSubject(op);
    std::string site = occurrence.site;
    if (site.empty()) {
      site = occurrence.operation;
      for (unsigned index : occurrence.position)
        site += "/" + std::to_string(index);
    }
    key.occurrence.emplace_back(std::move(site), occurrence.declaration);
  }
  return key;
}

inline VerificationDecision
verificationDecision(const finite::VerificationResult &result) {
  VerificationObservation outcome;
  switch (result.status) {
  case finite::VerificationStatus::Verified:
    outcome = VerificationObservation::Verified;
    break;
  case finite::VerificationStatus::Mismatch:
    outcome = VerificationObservation::Mismatch;
    break;
  case finite::VerificationStatus::OptionalCapacity:
    outcome = VerificationObservation::OptionalCapacity;
    break;
  case finite::VerificationStatus::RequiredCapacity:
    outcome = VerificationObservation::RequiredCapacity;
    break;
  }
  return {outcome, result.detail.str(), result.capacity, result.subject};
}

inline const char *decisionName(OptimizationStatus value) {
  switch (value) {
  case OptimizationStatus::Succeeded:
    return "succeeded";
  case OptimizationStatus::Unsupported:
    return "unsupported";
  case OptimizationStatus::MissingEvidence:
    return "missing-evidence";
  case OptimizationStatus::Capacity:
    return "capacity";
  case OptimizationStatus::PolicyDisabled:
    return "policy-disabled";
  case OptimizationStatus::ReplacementRestricted:
    return "replacement-restricted";
  case OptimizationStatus::MissingRecipe:
    return "missing-recipe";
  }
  llvm_unreachable("unknown mathematical decision");
}
inline const char *decisionName(OptimizationReason value) {
  switch (value) {
  case OptimizationReason::None:
    return "none";
  case OptimizationReason::Structure:
    return "structure";
  case OptimizationReason::Equation:
    return "equation";
  case OptimizationReason::EqualExtent:
    return "equal-extent";
  case OptimizationReason::StrictBound:
    return "strict-bound";
  case OptimizationReason::Depth:
    return "depth";
  case OptimizationReason::Cycle:
    return "cycle";
  case OptimizationReason::Replacement:
    return "replacement";
  case OptimizationReason::Recipe:
    return "recipe";
  case OptimizationReason::Policy:
    return "policy";
  case OptimizationReason::OrderedRetry:
    return "ordered-retry";
  case OptimizationReason::LaneFormula:
    return "lane-formula";
  case OptimizationReason::Work:
    return "work";
  case OptimizationReason::CallEligibility:
    return "call-eligibility";
  case OptimizationReason::ImplementationRestriction:
    return "implementation-restriction";
  }
  llvm_unreachable("unknown mathematical decision");
}
inline const char *decisionName(WorkOwner value) {
  switch (value) {
  case WorkOwner::Structural:
    return "structural";
  case WorkOwner::Equations:
    return "equations";
  case WorkOwner::Evidence:
    return "evidence";
  case WorkOwner::Lanes:
    return "lanes";
  case WorkOwner::OptionalComparison:
    return "optional-comparison";
  case WorkOwner::RequiredFiniteReader:
    return "required-finite-reader";
  case WorkOwner::HelperOperations:
    return "helper-operations";
  case WorkOwner::HelperSlots:
    return "helper-slots";
  case WorkOwner::Polynomial:
    return "polynomial";
  case WorkOwner::FiniteExpressions:
    return "finite-expressions";
  case WorkOwner::AlgorithmExpansion:
    return "algorithm-expansion";
  case WorkOwner::AlgorithmOriginBytes:
    return "algorithm-origin-bytes";
  case WorkOwner::AlgorithmChecking:
    return "algorithm-checking";
  }
  llvm_unreachable("unknown mathematical decision");
}
inline const char *decisionName(DecisionFamily value) {
  switch (value) {
  case DecisionFamily::Finite:
    return "finite";
  case DecisionFamily::NestedContraction:
    return "nested-contraction";
  case DecisionFamily::Lanes:
    return "lanes";
  case DecisionFamily::Map:
    return "map";
  case DecisionFamily::MapProduct:
    return "map-product";
  case DecisionFamily::VectorReduction:
    return "vector-reduction";
  }
  llvm_unreachable("unknown mathematical decision");
}
inline const char *decisionName(RealizationChoice value) {
  switch (value) {
  case RealizationChoice::Ordered:
    return "ordered";
  case RealizationChoice::Bilinear:
    return "bilinear";
  case RealizationChoice::Reduction:
    return "reduction";
  case RealizationChoice::Elementwise:
    return "elementwise";
  case RealizationChoice::NestedContraction:
    return "nested-contraction";
  case RealizationChoice::MapProduct:
    return "map-product";
  case RealizationChoice::MapSum:
    return "map-sum";
  }
  llvm_unreachable("unknown mathematical decision");
}
inline const char *decisionName(PublicationBoundary value) {
  switch (value) {
  case PublicationBoundary::IncorporatedIntoParent:
    return "incorporated-into-parent";
  case PublicationBoundary::ReturnedCandidate:
    return "returned-candidate";
  case PublicationBoundary::PublishedToCaller:
    return "published-to-caller";
  }
  llvm_unreachable("unknown mathematical decision");
}
inline const char *decisionName(CompletionKind value) {
  switch (value) {
  case CompletionKind::Completed:
    return "completed";
  case CompletionKind::Unchanged:
    return "unchanged";
  case CompletionKind::Refused:
    return "refused";
  }
  llvm_unreachable("unknown mathematical decision");
}

/// A journal scope observes existing transaction boundaries. It neither owns
/// candidates nor controls acceptance, retries, counters, or occurrence state.
class RealizationScope {
  RealizationTrace *trace;
  mlir::Operation *anchor;
  RealizationWork *work;
  uint64_t id = 0, parent = 0;
  std::string service;
  RealizationSubject subject;
  bool proposed = false, finished = false;
  DecisionCause failureCause = RequiredFailure{"service refused", {}};

  void append(RealizationEventPayload payload, const RealizationSubject &key) {
    if (!trace)
      return;
    trace->events.push_back({trace->events.size() + 1, id, parent, service, key,
                             std::move(payload)});
    const auto &event = trace->events.back();
    if (!trace->remarks && !trace->ir)
      return;
    std::string text;
    llvm::raw_string_ostream out(text);
    out << "mathematical decision " << event.sequence << " scope=" << id
        << " parent=" << parent << " service=" << service;
    if (!key.declaration.empty())
      out << " subject=@" << key.declaration;
    if (!key.site.empty())
      out << " site=" << key.site;
    std::visit([&](const auto &value) { render(out, value); }, event.payload);
    if (trace->remarks && anchor)
      anchor->emitRemark() << text;
    if (trace->ir)
      *trace->ir << "// " << text << "\n";
  }
  static void render(llvm::raw_ostream &out, const SelectionDecision &value) {
    out << " selection family=" << decisionName(value.family)
        << " choice=" << decisionName(value.choice)
        << " outcome=" << decisionName(value.outcome.status)
        << " reason=" << decisionName(value.outcome.reason);
    capacity(out, value.outcome.capacity);
  }
  static void capacity(llvm::raw_ostream &out,
                       const std::optional<CapacityCause> &cause) {
    if (!cause)
      return;
    out << " owner=" << decisionName(cause->owner);
    if (cause->requested)
      out << " requested=" << *cause->requested;
    if (cause->available)
      out << " available=" << *cause->available;
  }
  static void render(llvm::raw_ostream &out, const ProposalDecision &value) {
    out << " proposal finite-bulk=" << value.effectivePolicy.finiteBulk
        << " vector-reduction-fusion="
        << value.effectivePolicy.vectorReductionFusion;
  }
  static void render(llvm::raw_ostream &out, const DiscardDecision &value) {
    out << " discard";
    std::visit(
        [&](const auto &cause) {
          using T = std::decay_t<decltype(cause)>;
          if constexpr (std::is_same_v<T, OptimizationOutcome>)
            out << " outcome=" << decisionName(cause.status)
                << " reason=" << decisionName(cause.reason);
          else
            out << " reason=" << cause.detail;
          capacity(out, cause.capacity);
        },
        value.cause);
  }
  static void render(llvm::raw_ostream &out, const RetryDecision &value) {
    out << " retry discarded=" << value.discardedScope
        << " finite-bulk=" << value.effectivePolicy.finiteBulk;
  }
  static void render(llvm::raw_ostream &out, const PublicationDecision &value) {
    out << " publication=" << decisionName(value.boundary);
  }
  static void render(llvm::raw_ostream &out, const CompletionDecision &value) {
    out << " completion=" << decisionName(value.outcome);
    if (value.cause)
      render(out, DiscardDecision{*value.cause});
  }

public:
  bool enabled() const { return trace != nullptr; }
  RealizationScope(RealizationTrace *trace, llvm::StringRef service,
                   mlir::Operation *anchor,
                   MathematicalSelectionPolicy policy = {},
                   RealizationWork *work = nullptr,
                   std::optional<RealizationSubject> subject = {})
      : trace(trace), anchor(anchor), work(work), service(service.str()) {
    if (!trace)
      return;
    if (trace->activeScopes.empty()) {
      trace->policy = policy;
      trace->stages.clear();
      trace->events.clear();
      trace->nextScope = 1;
      trace->initialWork = work ? *work : RealizationWork{};
      trace->remainingWork = trace->initialWork;
    } else
      parent = trace->activeScopes.back();
    id = trace->nextScope++;
    trace->activeScopes.push_back(id);
    this->subject = subject ? std::move(*subject) : realizationSubject(anchor);
  }
  RealizationScope(const RealizationScope &) = delete;
  RealizationScope &operator=(const RealizationScope &) = delete;
  ~RealizationScope() {
    if (!trace)
      return;
    if (!finished) {
      if (proposed)
        discard(failureCause);
      else
        complete(CompletionKind::Refused);
    }
    if (work)
      trace->remainingWork = *work;
    trace->activeScopes.pop_back();
  }
  void propose() {
    propose(trace ? trace->policy : MathematicalSelectionPolicy{});
  }
  void propose(MathematicalSelectionPolicy effective) {
    if (trace) {
      proposed = true;
      append(ProposalDecision{effective}, subject);
    }
  }
  void selection(mlir::Operation *op, DecisionFamily family,
                 RealizationChoice choice, OptimizationOutcome outcome,
                 mlir::Operation *query = nullptr) {
    if (trace)
      selection(realizationSubject(op), family, choice, outcome,
                realizationSubject(query));
  }
  void selectionDiagnostic(mlir::Operation *op, DecisionFamily family,
                           RealizationChoice choice,
                           const finite::ComputationDiagnostic &diagnostic) {
    if (trace)
      selection(realizationSubject(op), family, choice, diagnostic.outcome,
                realizationSubject(diagnostic));
  }
  void selection(const RealizationSubject &key, DecisionFamily family,
                 RealizationChoice choice, OptimizationOutcome outcome,
                 RealizationSubject query = {}) {
    append(SelectionDecision{family, choice, outcome, std::move(query)}, key);
  }
  void failure(DecisionCause cause) { failureCause = std::move(cause); }
  void discard(DecisionCause cause) {
    append(DiscardDecision{std::move(cause)}, subject);
    finished = true;
  }
  void retry(MathematicalSelectionPolicy effective) {
    append(RetryDecision{id, effective}, subject);
  }
  void publish(PublicationBoundary boundary =
                   PublicationBoundary::IncorporatedIntoParent) {
    append(PublicationDecision{boundary}, subject);
    finished = true;
  }
  void complete(CompletionKind outcome = CompletionKind::Completed) {
    append(CompletionDecision{outcome,
                              outcome == CompletionKind::Refused
                                  ? std::optional<DecisionCause>(failureCause)
                                  : std::nullopt},
           subject);
    finished = true;
  }
};
} // namespace zkc::mathematical
#endif
