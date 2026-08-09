//===- Signature.h - Declarations and the record beside them ----*- C++ -*-===//
//
// A signature is the only place a theorem contribution is declared
// (docs/spec/soundness.md §5.4).  It pairs the executable catalog with the
// annotations kept beside it.
//
// The separation is structural rather than conventional: the kernel judgments
// receive a SoundnessCatalog and never a Signature, so an annotation cannot
// reach RULE_WF, APPLY, or DERIVE, and no digest over a declaration can pick
// one up.  Editing a citation therefore cannot re-mint a rule, and the presence
// of a citation cannot discharge a premise.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SIGNATURE_H
#define ZKC_SOUNDNESS_SIGNATURE_H

#include "zkc/Soundness/SoundnessCatalog.h"
#include "llvm/Support/Error.h"

#include <map>
#include <string>
#include <utility>
#include <vector>

namespace zkc::soundness {

/// One place in a cited source that states part of a declaration.
struct SourceAnchor {
  /// A stable external reference, such as an eprint number or a DOI.
  std::string source;
  /// The exact version read, for sources that have more than one.
  std::string revision;
  /// Where in that source the statement is, such as a theorem number.
  std::string anchor;
};

/// How much of a mechanized statement is actually established.
///
/// Three states rather than two, because a proof assistant admits a hole in
/// two independent places.  A statement whose proof is a hole is about the
/// right object and is not proved.  A statement whose *subject term* is a hole
/// would not be about the right object even if every proof were discharged,
/// and a format designed around citing a theorem does not anticipate that.
enum class FormalizationState {
  /// The reviewed dependency closure admits no axiom beyond the ambient ones.
  Mechanized,
  /// The statement exists; some step it rests on is admitted.
  ProofIncomplete,
  /// The statement exists; a term the statement is about is itself admitted.
  SubjectIncomplete,
};

const char *formalizationStateName(FormalizationState state);

/// A mechanized statement asserted to correspond to a declaration.
///
/// The receipt separates what a machine establishes from what a person
/// asserts.  A declaration's printed type and its axiom profile are obtainable
/// without proving anything and can be compared against the source again
/// later, so they are recorded facts and drift from them is detectable.  What
/// remains for a person is the correspondence itself, and the two `covers`
/// fields say how far it reaches.
struct FormalizationReceipt {
  std::string repository;
  std::string revision;
  /// The fully qualified declaration name inside that repository.
  std::string declaration;
  /// The declaration's type as the proof assistant prints it at that
  /// revision, whitespace-collapsed and transliterated into the
  /// printable-ASCII encoding domain (a registry string cannot carry the
  /// raw glyphs). Recorded so a later reading can recompute the same form
  /// and compare, rather than re-judge.
  std::string statement;
  /// The declaration's axiom profile as the proof assistant reports it. Empty
  /// means none were admitted, which is why this is a list: an empty string
  /// cannot distinguish "none" from "not recorded".
  std::vector<std::string> axioms;
  FormalizationState state = FormalizationState::ProofIncomplete;
  /// What this statement does establish about the declaration.
  std::string covers;
  /// What it does not — most often, where the rule is more general than the
  /// statement. A receipt that cannot say this overstates itself.
  std::string doesNotCover;
  /// Slots of the rule this statement has no counterpart for, named as the
  /// rule declares them. Checked when the signature is frozen, so the list
  /// cannot quietly fall out of step with the rule it is about.
  std::vector<std::string> unmatchedObligations;
};

/// A surveyed absence of a mechanized counterpart.
///
/// A receipt records a statement that exists; this records that one was
/// looked for and not found, so a rule without a receipt is not silent about
/// why.  It names the repository and revision that were read, the statement
/// the rule would cite in the author's words, and where the demand is
/// written down.  When the counterpart lands, the record is replaced by a
/// receipt rather than amended.
struct FormalizationAbsence {
  std::string repository;
  std::string revision;
  /// The statement the rule would cite, in the author's words.
  std::string wanted;
  /// Where the precise demand is recorded, as a repository-relative path.
  std::string demand;
};

/// Everything recorded beside a declaration and outside its digest.
struct DeclarationAnnotation {
  /// What the declaration says, in the author's words: the theorem a rule
  /// encodes, or the winning condition of a primitive game.  The executable
  /// form is the declaration itself; this is what a reader checks it against.
  std::string statement;
  /// The bound as an author would write it, for reading rather than
  /// evaluation.  The evaluated form is the rule body.
  std::string lossDisplay;
  /// Why the author chose the declaration's status.  Required when the status
  /// is not admitted, because an unreachable rule with no stated reason is a
  /// record nobody can act on.
  std::string statusRationale;
  /// Anything else a later reader needs and no other field holds.
  std::string notes;
  std::vector<std::string> citations;
  std::vector<SourceAnchor> statementBasis;
  std::vector<FormalizationReceipt> formalization;
  std::optional<FormalizationAbsence> formalizationAbsence;
};

/// An immutable signature: one executable catalog and its record.
class Signature {
public:
  const SoundnessCatalog catalog;
  const std::map<std::string, DeclarationAnnotation, std::less<>> annotations;

  Signature(const Signature &) = default;
  Signature(Signature &&) = default;
  Signature &operator=(const Signature &) = delete;
  Signature &operator=(Signature &&) = delete;

private:
  friend llvm::Expected<Signature> freezeSignature(
      SoundnessCatalog,
      std::map<std::string, DeclarationAnnotation, std::less<>>);

  Signature(SoundnessCatalog catalog,
            std::map<std::string, DeclarationAnnotation, std::less<>>
                annotations)
      : catalog(std::move(catalog)), annotations(std::move(annotations)) {}
};

/// Pair a frozen catalog with its annotations.
///
/// Every rule must carry an annotation naming at least one source anchor: a
/// rule whose statement cannot be located is one nobody can check, and the
/// requirement is what keeps a citation from being dropped when a declaration
/// is rewritten.  A non-admitted rule must additionally state why.  Every
/// annotation key must name something this signature declares — a rule, a
/// binding, a primitive game, a proposition, a machine decider, or a subject
/// schema — so a renamed declaration cannot leave its record orphaned.
/// Only rules are required to carry one: a binding connects a rule to protocol
/// structure and cites no source of its own.
llvm::Expected<Signature> freezeSignature(
    SoundnessCatalog catalog,
    std::map<std::string, DeclarationAnnotation, std::less<>> annotations);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SIGNATURE_H
