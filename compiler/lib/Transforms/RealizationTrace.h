#ifndef ZKC_TRANSFORMS_REALIZATIONTRACE_H
#define ZKC_TRANSFORMS_REALIZATIONTRACE_H

#include "FiniteVerification.h"
#include "RealizationSubject.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/Support/raw_ostream.h"
#include <cstddef>
#include <type_traits>

namespace zkc::mathematical {
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

/// A journal scope observes existing transaction boundaries. It neither owns
/// candidates nor controls acceptance, retries, counters, or occurrence state.
class RealizationScope {
  RealizationTrace *trace;
  mlir::Operation *anchor;
  RealizationWork *work;
  uint64_t id = 0, parent = 0;
  std::string service;
  RealizationSubject subject;
  std::size_t inheritedDeclarationOrigins = 0, visibleDeclarationOrigins = 0;
  bool proposed = false, finished = false;
  DecisionCause failureCause = RequiredFailure{"service refused", {}};

  // A child's overrides must not relabel an enclosing scope's own events.
  llvm::ArrayRef<std::pair<std::string, std::string>>
  declarationOrigins() const {
    return {trace->declarationOrigins.data(), visibleDeclarationOrigins};
  }
  void resolveCause(DecisionCause &cause) const {
    if (auto *verification = std::get_if<VerificationDecision>(&cause))
      verification->subject =
          sourceSubject(std::move(verification->subject), declarationOrigins());
  }
  void append(RealizationEventPayload payload, const RealizationSubject &key) {
    if (!trace)
      return;
    if (auto *selection = std::get_if<SelectionDecision>(&payload))
      selection->querySubject = sourceSubject(
          std::move(selection->querySubject), declarationOrigins());
    if (auto *discard = std::get_if<DiscardDecision>(&payload))
      resolveCause(discard->cause);
    if (auto *completion = std::get_if<CompletionDecision>(&payload);
        completion && completion->cause)
      resolveCause(*completion->cause);
    if (trace->events.size() >= trace->eventLimit) {
      ++trace->droppedEvents;
      return;
    }
    trace->events.push_back(
        {trace->events.size() + trace->droppedEvents + 1, id, parent, service,
         sourceSubject(key, declarationOrigins()), std::move(payload)});
    const auto &event = trace->events.back();
    if (!trace->remarks && !trace->ir)
      return;
    std::string text;
    llvm::raw_string_ostream out(text);
    out << "mathematical decision " << event.sequence << " scope=" << id
        << " parent=" << parent << " service=" << service;
    if (!event.subject.declaration.empty())
      out << " subject=@" << event.subject.declaration;
    if (!event.subject.site.empty())
      out << " site=" << event.subject.site;
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
        << value.effectivePolicy.vectorReductionFusion
        << " collect-fold-fusion=" << value.effectivePolicy.collectFoldFusion;
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
        << " finite-bulk=" << value.effectivePolicy.finiteBulk
        << " collect-fold-fusion=" << value.effectivePolicy.collectFoldFusion;
    if (value.occurrence)
      out << " occurrence=" << value.occurrence->declaration << ":"
          << value.occurrence->site;
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
      trace->droppedEvents = 0;
      trace->declarationOrigins.clear();
      trace->nextScope = 1;
      trace->initialWork = work ? *work : RealizationWork{};
      trace->remainingWork = trace->initialWork;
    } else
      parent = trace->activeScopes.back();
    id = trace->nextScope++;
    trace->activeScopes.push_back(id);
    inheritedDeclarationOrigins = visibleDeclarationOrigins =
        trace->declarationOrigins.size();
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
    trace->declarationOrigins.resize(inheritedDeclarationOrigins);
    trace->activeScopes.pop_back();
  }
  /// Register on the innermost scope. Nested observations inherit the mapping
  /// to an immutable declaration until this scope exits.
  void declarationOrigin(llvm::StringRef declaration, llvm::StringRef origin) {
    if (trace) {
      trace->declarationOrigins.emplace_back(declaration.str(), origin.str());
      visibleDeclarationOrigins = trace->declarationOrigins.size();
    }
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
  void retry(MathematicalSelectionPolicy effective,
             std::optional<RealizationSubject> occurrence = {}) {
    append(RetryDecision{id, effective, std::move(occurrence)}, subject);
  }
  void publish() {
    publish(parent ? PublicationBoundary::IncorporatedIntoParent
                   : PublicationBoundary::PublishedToCaller);
  }
  void publish(PublicationBoundary boundary) {
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
