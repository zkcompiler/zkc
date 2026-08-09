//===- DerivationEncoding.h - Asking for a derivation as data ---*- C++ -*-===//
//
// A derivation request and the witness it produces.
//
// The kernel's judgments are reached today only by constructing plan values in
// C++.  That is enough for a test and not enough for a consumer: nothing can be
// handed to someone, and nothing about a derivation outlives the process that
// ran it.  This is the data form of the question and of the answer.
//
// The witness records the question in full and the answer by digest.  A checker
// supplies its own signature, re-runs the derivation, and compares — it does
// not read the recorded conclusion and believe it.  What the witness carries in
// readable form is what a person has to act on: the bound, and the qualitative
// obligations the conclusion inherited.
//
// Values that the artifact supplies — a reduction contract, a path transition —
// are encoded by their exact reference rather than by their content.  The
// reference determines the content given the artifact, and the witness names
// the artifact, so the digest is faithful without restating the protocol.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_DERIVATIONENCODING_H
#define ZKC_SOUNDNESS_DERIVATIONENCODING_H

#include "zkc/Soundness/SoundnessEvaluator.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <string>
#include <vector>

namespace zkc::soundness {

/// Everything a derivation needs beyond the artifact and the signature.
struct DerivationRequest {
  /// Exact binding references the context selects, in the order given.
  std::vector<ExactRef> selectedBindingRefs;
  ResolvedParameterEnvironments resolvedParameters;
  DerivationTarget target;
  DerivationPlan plan;
};

/// Parse a request document against the signature it will be derived under.
///
/// Bindings are named by identifier and resolved here, so a request carries no
/// computed digest that can go stale, and one request can be run against a
/// second signature — which is what comparing two analyses of one artifact
/// needs. Fail-closed: unknown fields at any depth, a value sort a caller may
/// not supply, a binding this signature does not declare, or a malformed plan
/// node refuses.
llvm::Expected<DerivationRequest>
parseDerivationRequest(llvm::StringRef json, llvm::StringRef source,
                       const SoundnessCatalog &catalog);

/// A property a transform claimed to preserve on the way to this artifact.
///
/// The kernel does not know what a transform is, and does not need to. What it
/// needs is that a witness has somewhere to put an obligation whose author is
/// not a rule: the conclusion's own obligations are owned by the theorems the
/// derivation cited, and these are owned by the families that produced the
/// artifact. Different authors, so a different place.
///
/// `LEGAL` never checks one (docs/spec/compiler.md §7.2), so a reader holding
/// a preservation obligation has been told whose argument to go and read, not
/// told that the property holds. A derivation about an artifact nobody
/// transformed has none, and the section is then empty rather than absent.
struct PreservationObligation {
  std::string property;
  ExactRef familyRef;
  uint64_t applicationIndex = 0;
};

/// The canonical document for one judgment, for digesting and comparison.
llvm::json::Value encodeJudgmentDocument(const SecurityJudgment &judgment);

/// The derivation with every bound removed: the plan's shape, each node's site
/// and binding, and the part of each conclusion that structure alone
/// determines — its subject, its index, its resource variables, and the
/// qualitative obligations it inherited.
///
/// This is a comparison view rather than a semantic object.  It exists because
/// the reference twin mirrors the structural and typing half of `DERIVE` and
/// not numeric bound composition, so it is deliberately the largest projection
/// the two implementations compare byte for byte.
llvm::json::Value encodeDerivationSkeleton(const DerivationResult &result);

/// `sha256:` reference over that document. Two derivations agree exactly when
/// this agrees.
llvm::Expected<std::string> judgmentDigest(const SecurityJudgment &judgment);

/// The witness document: the question in full, the answer by digest, and the
/// part of the answer a reader has to act on.
llvm::Expected<llvm::json::Value>
encodeWitness(llvm::StringRef artifactId, llvm::StringRef signatureDigest,
              const DerivationRequest &request, const DerivationResult &result,
              llvm::ArrayRef<PreservationObligation> preservation = {},
              llvm::ArrayRef<std::pair<std::string, bool>>
                  subjectAnchorGrounding = {});

/// The parts of a witness a checker compares against its own derivation.
struct WitnessClaim {
  std::string artifactId;
  std::string signatureDigest;
  std::string judgmentDigest;
  DerivationRequest request;
  /// Carried through rather than re-derived: a checker has the artifact and
  /// the signature, not the trace that produced the artifact, so what it can
  /// do with a preservation obligation is repeat who claimed it.
  std::vector<PreservationObligation> preservation;
  /// The recorded grounded/declared spelling of the target claim's anchors.
  /// Unlike a preservation obligation this is artifact-derived, so a checker
  /// recomputes it from its own view and refuses a witness that disagrees.
  std::vector<std::pair<std::string, std::string>> subjectAnchorGrounding;
};

llvm::Expected<WitnessClaim> parseWitness(llvm::StringRef json,
                                          llvm::StringRef source,
                                          const SoundnessCatalog &catalog);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_DERIVATIONENCODING_H
