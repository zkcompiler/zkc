//===- zkc-derive.cpp - derive a conditional security judgment --*- C++ -*-===//
//
// The first consumer of the Soundness Kernel outside a test, and the first
// place a judgment outlives the process that produced it.
//
// Two modes. Producing takes an admitted artifact, a signature and a request,
// runs the derivation, and writes a witness. Checking takes a witness and a
// signature, runs the same derivation under the signature the CHECKER supplies,
// and compares digests. It never reads the recorded conclusion and believes it;
// that is what makes the witness worth handing to someone.
//
// The signature the checker supplies may differ from the producer's. When it
// does, the check says so and still reports what it derived, because that is
// the interesting case: the artifact is the same protocol under both, and the
// two analyses are comparable exactly because both remain keyed to that same
// content-addressed artifact.
//
//===----------------------------------------------------------------------===//

#include "zkc/Artifact/Artifact.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Registry/Rational.h"
#include "zkc/Soundness/DerivationEncoding.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "zkc/Soundness/SignatureEncoding.h"
#include "zkc/Soundness/SignatureFile.h"
#include "zkc/Soundness/SoundnessEvaluator.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/ToolOutputFile.h"

namespace cl = llvm::cl;
namespace snd = zkc::soundness;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<PIR artifact>"));
static cl::opt<std::string>
    signatureFilename("signature", cl::Required,
                      cl::desc("The signature to derive against"));
static cl::opt<std::string> vocabularyFilename("protocol-vocabulary",
                                               cl::Required,
                                               cl::desc("Protocol vocabulary"));
static cl::opt<std::string>
    profileFilename("construction-profile-registry", cl::Required,
                    cl::desc("Construction-profile registry"));
static cl::opt<std::string>
    requestFilename("request", cl::desc("Derivation request (JSON)"));
static cl::opt<std::string>
    checkFilename("check", cl::desc("Witness to re-derive and compare"));
static cl::opt<std::string> outputFilename("o", cl::init("-"),
                                           cl::desc("Where the witness goes"));
static cl::opt<bool>
    describe("describe",
             cl::desc("List the application sites this artifact offers"));
static cl::opt<bool> skeleton(
    "skeleton",
    cl::desc("With --request, print the derivation without its bounds"));
static cl::opt<bool> headline(
    "headline",
    cl::desc("With --request, also print a display summary: per-round "
             "loss ceilings in bits, their minimum, and the obligations "
             "ledger. Display only — the witness stays exact"));

namespace {

int fail(const llvm::Twine &message) {
  return zkc::tool::reportRefusal(llvm::createStringError(message));
}

int failError(llvm::Error error) {
  return zkc::tool::reportRefusal(std::move(error));
}

std::string refusalText(const snd::SoundnessRefusal &refusal) {
  return std::string(snd::runtimePhaseName(refusal.phase)) + "/" +
         snd::runtimeRefusalCodeName(refusal.code) + " at " + refusal.location +
         ": " + refusal.detail;
}

} // namespace

int main(int argc, char **argv) {
  llvm::InitLLVM initLlvm(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv,
      "zkc-derive: derive a conditional security "
      "judgment about a sealed protocol\n\n\nExit: 0 the answer is yes, 1 the "
      "subject was examined and the answer is no, 2 the invocation never "
      "reached its subject (docs/getting-started.md).\n");

  if (skeleton && requestFilename.empty())
    return fail("--skeleton needs a --request");
  if (!describe && requestFilename.empty() == checkFilename.empty())
    return fail("give exactly one of --request, --check and --describe");

  auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
      vocabularyFilename, profileFilename);
  if (!environment)
    return failError(environment.takeError());
  auto artifact = zkc::artifact::loadAndAdmitArtifact(inputFilename,
                                                      std::move(*environment));
  if (!artifact)
    return failError(artifact.takeError());
  auto view = snd::buildSealedSoundnessView(*artifact);
  if (!view)
    return failError(view.takeError());

  // A request names claims by their exact descriptor digest, which is derived
  // rather than written in the artifact. A tool that demands one and cannot
  // report it is not usable, so it reports them.
  if (describe) {
    llvm::outs() << "artifact: " << view->artifactId << "\n";
    for (const auto &[position, reduction] :
         view->reductionsByTransformerPosition) {
      for (size_t output = 0; output < reduction.orderedOutputs.size();
           ++output) {
        const snd::ClaimRef &claim = reduction.orderedOutputs[output];
        llvm::outs() << "reduction site: transformer " << position << " output "
                     << output << " claim " << claim.claimIndex << " "
                     << claim.descriptorDigest << "\n";
        llvm::outs() << "path site: claim " << claim.claimIndex << " "
                     << claim.descriptorDigest << "\n";
      }
    }
    // The bodies the sealed view projects. A consumer asking whether two
    // transformers commute needs the footprint, and no judgment here reads
    // it, so this is where it becomes visible -- and where the two
    // implementations are compared on it.
    for (const snd::TransformerExtent &body : view->transformerBodies)
      llvm::outs() << "transformer body: " << body.instance << " events "
                   << body.begin << ".." << body.end
                   << (body.central ? " central" : " non-central") << "\n";
    return 0;
  }

  auto signature = snd::loadSignatureFromFile(signatureFilename);
  if (!signature)
    return failError(signature.takeError());
  auto signatureDigest = snd::signatureDigest(signature->catalog);
  if (!signatureDigest)
    return failError(signatureDigest.takeError());

  const bool checking = !checkFilename.empty();
  llvm::StringRef documentPath = checking ? checkFilename : requestFilename;
  auto document = llvm::MemoryBuffer::getFile(documentPath);
  if (!document)
    return fail("cannot read '" + documentPath +
                "': " + document.getError().message());

  snd::DerivationRequest request;
  snd::WitnessClaim claim;
  if (checking) {
    auto parsedWitness = snd::parseWitness((*document)->getBuffer(),
                                           documentPath, signature->catalog);
    if (!parsedWitness)
      return failError(parsedWitness.takeError());
    claim = std::move(*parsedWitness);
    request = claim.request;
    if (claim.artifactId != view->artifactId)
      return fail("the witness is about artifact " + claim.artifactId +
                  " and this is " + view->artifactId);
  } else {
    auto parsedRequest = snd::parseDerivationRequest(
        (*document)->getBuffer(), documentPath, signature->catalog);
    if (!parsedRequest)
      return failError(parsedRequest.takeError());
    request = std::move(*parsedRequest);
  }

  snd::SoundnessContextOutcome soundnessContext = snd::buildSoundnessContext(
      signature->catalog, request.selectedBindingRefs,
      request.resolvedParameters);
  if (!soundnessContext.accepted())
    return fail("the selected context is ill-formed: " +
                refusalText(*soundnessContext.refusal));

  snd::DeriveOutcome outcome = snd::deriveSoundness(
      *soundnessContext.context, *view, request.target, request.plan);
  if (!outcome.accepted())
    return fail("derivation refused: " + refusalText(*outcome.refusal));

  // The reference twin mirrors the structural and typing half of the judgment,
  // not numeric composition, so this is deliberately the largest projection
  // the two implementations compare byte for byte.
  if (skeleton) {
    std::error_code error;
    llvm::ToolOutputFile out(outputFilename, error, llvm::sys::fs::OF_Text);
    if (error)
      return fail("cannot write '" + outputFilename + "': " + error.message());
    if (llvm::Error err = zkc::encoding::writeCanonicalJson(
            snd::encodeDerivationSkeleton(*outcome.result), out.os()))
      return failError(std::move(err));
    out.keep();
    return 0;
  }

  // The grounded/declared spelling of the target claim's anchors, projected
  // for the witness reader: the conclusion below stands on these anchors, and
  // which of them are tied to a transcript position and which are their
  // authors' declaration is a fact of the artifact, recomputable by any
  // checker.  It is never consulted by the judgment.
  std::vector<std::pair<std::string, bool>> grounding;
  if (const auto *protocolClaim = std::get_if<snd::ProtocolClaimSubject>(
          &request.target.subject.payload)) {
    uint64_t index = protocolClaim->claim.claimIndex;
    if (index < view->claimAnchorsByIndex.size())
      for (const auto &[anchor, valueRef] : view->claimAnchorsByIndex[index])
        grounding.emplace_back(anchor,
                               view->boundMaterialRefs.count(valueRef) != 0);
  }

  // Whether the derivation covers the artifact, not one site of it. Every
  // line above is about a step; a consumer wants to know that the whole
  // thing is discharged, and until now nothing said it.
  if (const auto *protocolClaim = std::get_if<snd::ProtocolClaimSubject>(
          &request.target.subject.payload)) {
    snd::ArtifactJudgment artifact = snd::judgeArtifact(
        *view, protocolClaim->claim,
        snd::derivationCoverage(*view, *outcome.result));
    llvm::outs() << "artifact judgment: "
                 << (artifact.discharged ? "discharged" : "not discharged")
                 << " (policy " << artifact.policy << ")\n";
    for (uint64_t index : artifact.uncoveredClaims)
      llvm::outs() << "artifact judgment: claim " << index
                   << " is neither consumed nor the derivation's target\n";
    for (uint64_t position : artifact.uncoveredChallenges)
      llvm::outs() << "artifact judgment: the challenge at event " << position
                   << " belongs to no transformer this derivation covers, so "
                      "its round is not in the bound\n";
  }

  auto witness = snd::encodeWitness(view->artifactId, *signatureDigest, request,
                                    *outcome.result, {}, grounding);
  if (!witness)
    return failError(witness.takeError());

  if (checking) {
    const llvm::json::Object *identity =
        witness->getAsObject()->getObject("identity");
    llvm::StringRef derived = *identity->getString("judgment_digest");
    // The signature is the checker's, so a different one is not an error: it
    // is a different analysis of the same protocol, and saying which it was is
    // the point of naming both.
    if (claim.signatureDigest != *signatureDigest)
      llvm::outs() << "signature: recorded " << claim.signatureDigest
                   << ", checking under " << *signatureDigest << "\n";
    else
      llvm::outs() << "signature: " << *signatureDigest << "\n";
    llvm::outs() << "artifact: " << view->artifactId << "\n";
    // Repeated, not re-derived. A checker holds the artifact and the
    // signature, not the trace that produced the artifact, so what it can
    // establish about a preservation claim is who made it.
    for (const snd::PreservationObligation &obligation : claim.preservation)
      llvm::outs() << "preservation: " << obligation.property << " claimed by "
                   << obligation.familyRef.id << " at application "
                   << obligation.applicationIndex << ", not checked here\n";
    // Grounding is artifact-derived, unlike a preservation claim, so a
    // witness that disagrees with the artifact about it is wrong.
    std::vector<std::pair<std::string, std::string>> derivedGrounding;
    for (const auto &[anchor, grounded] : grounding)
      derivedGrounding.emplace_back(anchor, grounded ? "grounded" : "declared");
    if (claim.subjectAnchorGrounding != derivedGrounding) {
      llvm::outs() << "zkc-derive: witness disagrees with the artifact about "
                      "anchor grounding\n";
      return 1;
    }
    if (derived == claim.judgmentDigest) {
      llvm::outs() << "judgment: " << derived << "\n";
      llvm::outs() << "zkc-derive: witness re-derives\n";
      return 0;
    }
    llvm::outs() << "judgment: recorded " << claim.judgmentDigest
                 << ", derived " << derived << "\n";
    llvm::outs() << "zkc-derive: witness does not re-derive\n";
    return 1;
  }

  // Writing the exact witness is the tool's product, and every path below
  // reaches it: a display that returned early would let --headline decide
  // whether the witness exists.
  auto finish = [&]() -> int {
    std::error_code error;
    llvm::ToolOutputFile out(outputFilename, error, llvm::sys::fs::OF_Text);
    if (error)
      return fail("cannot write '" + outputFilename + "': " + error.message());
    out.os() << llvm::formatv("{0:2}", *witness) << "\n";
    out.keep();
    return 0;
  };

  // The display view: presentation of the exact witness, never a
  // judgment of its own. Each round's loss is shown as a power-of-two
  // ceiling (epsilon rounds up, so the shown exponent never overstates
  // security), the headline is the weakest round, and the obligations
  // ledger rides beside the number — a bound without its assumptions
  // is not this tool's product.
  if (headline) {
    const llvm::json::Object *conclusion =
        witness->getAsObject()->getObject("conclusion");
    const llvm::json::Object *result =
        conclusion ? conclusion->getObject("result") : nullptr;
    const llvm::json::Array *rounds =
        result ? result->getArray("rounds") : nullptr;
    // A compiled conclusion is one bound over the whole transcript rather
    // than a round sequence, and it is the judgment a reader of this tool
    // came for. Each term is shown at its own ceiling instead of being
    // summed: t and tau are the adversary's resources, so a single number
    // would need values for them that no rule supplied.
    const llvm::json::Object *scalar =
        rounds ? nullptr : (result ? result->getObject("bound") : nullptr);
    // A completeness judgment also concludes in one bound, and displaying it
    // beside the soundness ones would let an honest-prover failure rate read
    // as an adversary's advantage. The track is what separates them, so it is
    // what this reads -- the shape does not.
    const llvm::json::Object *index = conclusion->getObject("index");
    llvm::StringRef track = index ? *index->getString("track") : "";
    const bool security = track == "soundness" || track == "knowledge";
    if (!security)
      return fail("--headline displays a security bound; this witness "
                  "concludes on the " +
                  track + " track");
    if (!rounds && !scalar)
      return fail("--headline displays a bound; this witness carries no "
                  "round sequence and no scalar bound");
    if (scalar) {
      const llvm::json::Object *quantity = scalar->getObject("quantity");
      auto show = [&](llvm::StringRef term, llvm::StringRef constant) -> bool {
        auto [num, den] = constant.split('/');
        auto value = den.empty()
                         ? zkc::registry::Rational::fromDecimal(num)
                         : zkc::registry::Rational::fromDecimalPair(num, den);
        if (!value) {
          llvm::consumeError(value.takeError());
          return false;
        }
        if (value->isZero())
          return true;
        auto ceiling = value->ceilLog2();
        if (!ceiling) {
          llvm::consumeError(ceiling.takeError());
          return false;
        }
        llvm::outs() << "headline term " << term << ": <= 2^" << *ceiling
                     << "\n";
        return true;
      };
      if (!show("constant", *quantity->getString("constant")))
        return fail("--headline cannot display this witness's constant term");
      if (const llvm::json::Array *terms =
              quantity->getArray("resource_terms"))
        for (const llvm::json::Value &entry : *terms) {
          const llvm::json::Object *term = entry.getAsObject();
          llvm::StringRef name = *term->getString("resource");
          int64_t exponent = *term->getInteger("exponent");
          std::string label =
              exponent == 1 ? name.str()
                            : (name + "^" + llvm::Twine(exponent)).str();
          if (!show(label, *term->getString("coefficient")))
            return fail("--headline cannot display this witness's " + label +
                        " term");
        }
      // A game advantage has no numeric ceiling to show: it is an assumption
      // the bound rests on, scaled by a count this artifact carries.
      if (const llvm::json::Array *games =
              scalar->getArray("primitive_game_terms"))
        for (const llvm::json::Value &entry : *games) {
          const llvm::json::Object *game = entry.getAsObject();
          llvm::outs() << "headline term " << *game->getObject("game")
                                                  ->getString("id")
                       << ": " << *game->getString("coefficient")
                       << " x its advantage\n";
        }
      if (const llvm::json::Array *obligations =
              conclusion->getArray("qualitative_obligations"))
        for (const llvm::json::Value &entry : *obligations)
          llvm::outs() << "headline obligation: " << *entry.getAsString()
                       << "\n";
      return finish();
    }
    std::optional<int64_t> weakest;
    for (const llvm::json::Value &entry : *rounds) {
      const llvm::json::Object *round = entry.getAsObject();
      llvm::StringRef index = *round->getString("round_index");
      const llvm::json::Object *quantity =
          round->getObject("bound")->getObject("quantity");
      if (const llvm::json::Array *terms = quantity->getArray("resource_terms"))
        if (!terms->empty())
          return fail("--headline displays constant bounds; this witness's "
                      "round " +
                      llvm::Twine(index) +
                      " carries resource terms the display would drop");
      llvm::StringRef constant = *quantity->getString("constant");
      auto [num, den] = constant.split('/');
      auto value = den.empty()
                       ? zkc::registry::Rational::fromDecimal(num)
                       : zkc::registry::Rational::fromDecimalPair(num, den);
      if (!value)
        return failError(value.takeError());
      if (value->isZero()) {
        llvm::outs() << "headline round " << index << ": eps = 0\n";
        continue;
      }
      auto ceiling = value->ceilLog2();
      if (!ceiling)
        return failError(ceiling.takeError());
      llvm::outs() << "headline round " << index << ": eps <= 2^" << *ceiling
                   << "\n";
      if (!weakest || *ceiling > *weakest)
        weakest = *ceiling;
    }
    if (weakest)
      llvm::outs() << "headline: the weakest round loses at most 2^" << *weakest
                   << " per attempt\n";
    if (const llvm::json::Array *obligations =
            conclusion->getArray("qualitative_obligations"))
      for (const llvm::json::Value &entry : *obligations)
        llvm::outs() << "headline obligation: " << *entry.getAsString() << "\n";
  }

  return finish();
}
