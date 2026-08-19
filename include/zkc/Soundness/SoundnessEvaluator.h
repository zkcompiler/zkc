//===- SoundnessEvaluator.h - Executable soundness judgments ----*- C++ -*-===//
//
// APPLY and DERIVE for the owned Soundness Kernel.  The evaluator is a closed,
// representation-neutral trusted-input interpreter: callers must authenticate
// the SealedSoundnessView through their representation authority before entry.
// It retains no MLIR object, registry handle, callback, policy hook, evidence
// object, or certificate representation.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SOUNDNESSEVALUATOR_H
#define ZKC_SOUNDNESS_SOUNDNESSEVALUATOR_H

#include "zkc/Soundness/SealedSoundnessView.h"
#include "zkc/Soundness/SoundnessCatalog.h"
#include "zkc/Soundness/SoundnessKernel.h"
#include "zkc/Soundness/SoundnessRuntime.h"
#include "llvm/ADT/ArrayRef.h"

#include <map>
#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace zkc::soundness {

/// The external values available to one exact selected binding.  The outer
/// map in SoundnessContext is keyed by `bindingRef.id`; the complete reference
/// here prevents a same-id/different-revision parameter environment.
struct ResolvedParameterEnvironment {
  ExactRef bindingRef;
  std::map<std::string, RuntimeValue, std::less<>> values;
};

using ResolvedParameterEnvironments =
    std::map<std::string, ResolvedParameterEnvironment, std::less<>>;

class SoundnessContext;
struct SoundnessContextOutcome;

/// Validate and own one complete executable selection.  A context is returned
/// only after every selected binding and external parameter has been checked.
SoundnessContextOutcome
buildSoundnessContext(const SoundnessCatalog &catalog,
                      std::vector<ExactRef> selectedBindingRefs,
                      ResolvedParameterEnvironments resolvedParameters = {});

/// A closed, immutable selection of executable semantics.
///
/// The context owns a catalog snapshot rather than caller-owned rule or
/// binding values.  Selected bindings are the sole executable authority; each
/// binding determines its rule through `ruleRef`.  A catalog rule with no
/// selected binding remains a declaration and is not executable.  Context WF
/// rejects absent, duplicate, or inconsistent selections and unresolved or
/// surplus external parameters.
class SoundnessContext {
public:
  SoundnessContext(const SoundnessContext &) = default;
  SoundnessContext(SoundnessContext &&) = default;
  SoundnessContext &operator=(const SoundnessContext &) = delete;
  SoundnessContext &operator=(SoundnessContext &&) = delete;

  const SoundnessCatalog &catalog() const { return catalog_; }
  const SchemaContext &schemas() const { return catalog_.schemas; }
  llvm::ArrayRef<ExactRef> selectedBindingRefs() const {
    return selectedBindingRefs_;
  }
  const ResolvedParameterEnvironments &resolvedParameters() const {
    return resolvedParameters_;
  }

  /// Return a rule only when some exact selected binding names it. Return a
  /// binding only when its complete reference is explicitly selected.
  const SoundnessRule *findRule(const ExactRef &ref) const;
  const RuleBinding *findBinding(const ExactRef &ref) const;
  const ResolvedParameterEnvironment *
  findResolvedParameters(const ExactRef &bindingRef) const;

private:
  SoundnessContext(const SoundnessCatalog &catalog,
                   std::vector<ExactRef> selectedBindingRefs,
                   ResolvedParameterEnvironments resolvedParameters);

  friend SoundnessContextOutcome
  buildSoundnessContext(const SoundnessCatalog &catalog,
                        std::vector<ExactRef> selectedBindingRefs,
                        ResolvedParameterEnvironments resolvedParameters);

  SoundnessCatalog catalog_;
  std::vector<ExactRef> selectedBindingRefs_;
  ResolvedParameterEnvironments resolvedParameters_;
};

struct SoundnessContextOutcome {
  std::optional<SoundnessContext> context;
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return context.has_value() && !refusal.has_value(); }
};

/// APPLY's premise inputs are already evaluated judgments, indexed exactly by
/// the consuming rule's premise-port names.  DERIVE is responsible for
/// creating the canonical assumption marker on an Assume leaf.
using TypedPremiseJudgments =
    std::map<std::string, SecurityJudgment, std::less<>>;

struct AppliedJudgment {
  ApplicationSite site;
  ExactRef bindingRef;
  TypedPremiseJudgments specializedPremises;
  SecurityJudgment conclusion;
};

struct ApplyOutcome {
  std::optional<AppliedJudgment> applied;
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return applied.has_value() && !refusal.has_value(); }
};

/// Interpret one rule application over an already authenticated semantic view.
/// This low-level function deliberately does not authenticate a representation;
/// public orchestration boundaries must establish that precondition.
ApplyOutcome applySoundnessRule(const SoundnessContext &context,
                                const SealedSoundnessView &sealed,
                                const ApplicationSite &site,
                                const ExactRef &bindingRef,
                                const TypedPremiseJudgments &premises);

struct DerivationPlan;

struct ExternalJudgmentAssumption {
  SecurityJudgment assertedJudgment;
};

struct ApplyDerivationPlan {
  ApplicationSite site;
  ExactRef bindingRef;
  std::map<std::string, std::shared_ptr<const DerivationPlan>, std::less<>>
      premises;
};

/// Shared child pointers permit callers to memoize equal plan subtrees.  The
/// evaluator still interprets every incoming premise occurrence and rejects a
/// null child or an active-pointer cycle.
struct DerivationPlan {
  using Node = std::variant<ExternalJudgmentAssumption, ApplyDerivationPlan>;
  Node node = ExternalJudgmentAssumption();
};

struct EvaluatedDerivation;

struct EvaluatedAssumption {
  SecurityJudgment input;
  SecurityJudgment conclusion;
};

struct EvaluatedApplication {
  ApplicationSite site;
  ExactRef bindingRef;
  std::map<std::string, std::shared_ptr<const EvaluatedDerivation>, std::less<>>
      premises;
  SecurityJudgment conclusion;
};

struct EvaluatedDerivation {
  using Node = std::variant<EvaluatedAssumption, EvaluatedApplication>;
  Node node = EvaluatedAssumption();
};

struct DerivationTarget {
  SecuritySubject subject;
  SecurityIndex index;
  std::vector<TypedDeclaration> resourceVariables;
};

struct DerivationResult {
  std::string artifactId;
  DerivationTarget target;
  EvaluatedDerivation root;
};

struct DeriveOutcome {
  std::optional<DerivationResult> result;
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return result.has_value() && !refusal.has_value(); }
};

/// Interpret a rooted plan over an already authenticated semantic view.  Like
/// APPLY, this is a trusted-input kernel API rather than a representation
/// authentication boundary.
DeriveOutcome deriveSoundness(const SoundnessContext &context,
                              const SealedSoundnessView &sealed,
                              const DerivationTarget &target,
                              const DerivationPlan &plan);

/// What of an artifact an evaluated derivation reached, for the artifact
/// judgment to weigh against the spine. See `DerivationCoverage`: reduction
/// occurrences cover their transformer, path occurrences cover the producer
/// of the claim they name, and assumptions cover nothing.
DerivationCoverage derivationCoverage(const SealedSoundnessView &sealed,
                                      const DerivationResult &result);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SOUNDNESSEVALUATOR_H
