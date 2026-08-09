//===- Signature.cpp - Declarations and the record beside them ----------===//
#include "zkc/Soundness/Signature.h"

#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"

#include <set>
#include <string>
#include <utility>

namespace zkc::soundness {

namespace {

llvm::Error signatureError(const llvm::Twine &message) {
  return llvm::createStringError(message);
}

} // namespace

llvm::Expected<Signature> freezeSignature(
    SoundnessCatalog catalog,
    std::map<std::string, DeclarationAnnotation, std::less<>> annotations) {
  for (const auto &[id, annotation] : annotations) {
    (void)annotation;
    const bool declared = catalog.rules.count(id) != 0 ||
                          catalog.bindings.count(id) != 0 ||
                          catalog.schemas.primitiveGames.count(id) != 0 ||
                          catalog.schemas.propositions.count(id) != 0 ||
                          catalog.schemas.machineDeciders.count(id) != 0 ||
                          catalog.schemas.subjectSchemas.count(id) != 0;
    if (!declared)
      return signatureError("annotation '" + id +
                            "' names nothing this signature declares");
  }

  for (const auto &[id, rule] : catalog.rules) {
    auto annotation = annotations.find(id);
    if (annotation == annotations.end())
      return signatureError("rule '" + id + "' carries no annotation");
    if (annotation->second.statementBasis.empty())
      return signatureError("rule '" + id + "' names no source anchor");
    for (const SourceAnchor &basis : annotation->second.statementBasis) {
      if (basis.source.empty() || basis.anchor.empty())
        return signatureError("rule '" + id +
                              "' has a source anchor without a source or a "
                              "location inside it");
    }
    if (rule.status != RuleStatus::Admitted &&
        annotation->second.statusRationale.empty())
      return signatureError("rule '" + id + "' is " +
                            ruleStatusName(rule.status) +
                            " without stating why");

    std::set<std::string> slots;
    for (const MachineConditionTemplate &condition : rule.machineConditions)
      slots.insert(condition.slot);
    for (const ExternalHypothesisTemplate &hypothesis : rule.externalHypotheses)
      slots.insert(hypothesis.slot);
    for (const FormalizationReceipt &receipt :
         annotation->second.formalization) {
      if (receipt.declaration.empty())
        return signatureError("rule '" + id +
                              "' has a formalization receipt naming no "
                              "declaration");
      // An empty axiom list is the claim that none were admitted, so it may
      // not sit beside a state that says otherwise, and a state of mechanized
      // may not sit beside an admitted hole.
      const bool admitsHole =
          llvm::is_contained(receipt.axioms, "sorryAx") ||
          llvm::is_contained(receipt.axioms, "sorry");
      if ((receipt.state == FormalizationState::Mechanized) == admitsHole)
        return signatureError(
            "rule '" + id + "' has a formalization receipt recorded as " +
            formalizationStateName(receipt.state) +
            " whose axiom profile says the opposite");
      // The unmatched list is about this rule, so it may only name slots this
      // rule declares. A renamed slot then surfaces here rather than leaving a
      // stale claim about coverage.
      for (const std::string &slot : receipt.unmatchedObligations)
        if (slots.count(slot) == 0)
          return signatureError("rule '" + id +
                                "' has a formalization receipt naming '" +
                                slot + "', which the rule does not declare");
    }
    // The catalog stays total: a rule must say what the mechanization holds
    // for it, or that a counterpart was looked for and not found.
    if (annotation->second.formalization.empty() &&
        !annotation->second.formalizationAbsence)
      return signatureError("rule '" + id +
                            "' records neither a formalization receipt nor "
                            "a surveyed absence");
  }

  return Signature(std::move(catalog), std::move(annotations));
}

const char *formalizationStateName(FormalizationState state) {
  switch (state) {
  case FormalizationState::Mechanized:
    return "mechanized";
  case FormalizationState::ProofIncomplete:
    return "proof_incomplete";
  case FormalizationState::SubjectIncomplete:
    return "subject_incomplete";
  }
  return "unknown";
}

} // namespace zkc::soundness
