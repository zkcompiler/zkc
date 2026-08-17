//===- zkc-relation.cpp - The correspondence judgment -----------*- C++ -*-===//
// Given a sealed artifact, a RelationContract, and optionally the
// relation-artifact bytes, reports what the correspondence judgment
// establishes (docs/spec/relations.md §4). The output's shape is the
// point: computed facts, cross-checked agreements, and the asserted
// remainder are reported as three separate lists, so no reader can take
// the judgment for a statement that the relation is verified.
//===----------------------------------------------------------------------===//

#include "zkc/Artifact/Artifact.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Registry/RelationContractRegistry.h"
#include "zkc/Relation/R1csHeader.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "zkc/Soundness/SealedSoundnessView.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace snd = zkc::soundness;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<sealed artifact>"));
static cl::opt<std::string>
    contractsFilename("contracts", cl::Required,
                      cl::desc("Relation-contract registry"));
static cl::opt<std::string> contractName("contract", cl::Required,
                                         cl::desc("Contract entry to judge"));
static cl::opt<std::string>
    vocabularyFilename("protocol-vocabulary", cl::Required,
                       cl::desc("Protocol vocabulary registry"));
static cl::opt<std::string>
    profileFilename("construction-profile-registry", cl::Required,
                    cl::desc("Construction profile registry"));
static cl::opt<std::string>
    bytesFilename("relation-bytes", cl::init(""),
                  cl::desc("Relation-artifact bytes, read per the format"));
static cl::opt<std::string>
    fieldOrder("declared-field-order", cl::init(""),
               cl::desc("The field a derivation over this artifact declares"));

static int fail(const Twine &message) {
  errs() << "error: " << message << "\n";
  return 1;
}
static int failError(Error err) { return zkc::tool::reportError(std::move(err)); }

namespace {
/// The judgment's three lists. Keeping them apart in the type is what
/// keeps them apart in the output.
struct Report {
  std::vector<std::string> computed;
  std::vector<std::string> crossChecked;
  std::vector<std::string> asserted;
};

/// The digest of the empty input: an anchor carrying it makes the scope
/// gate vacuous, which the judgment says rather than counting as met
/// (docs/spec/relations.md §2.3).
constexpr StringLiteral kEmptyInputDigest =
    "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
} // namespace

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv, "zkc-relation: the relation correspondence judgment\n");

  auto contracts = zkc::registry::RelationContractRegistry::loadFromFile(
      contractsFilename);
  if (!contracts)
    return failError(contracts.takeError());
  const zkc::registry::RelationContract *contract =
      contracts->lookup(contractName);
  if (!contract)
    return fail("no relation contract '" + contractName + "' in " +
                contractsFilename);

  auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
      vocabularyFilename, profileFilename);
  if (!environment)
    return failError(environment.takeError());
  auto artifact =
      zkc::artifact::loadAndAdmitArtifact(inputFilename, std::move(*environment));
  if (!artifact)
    return failError(artifact.takeError());
  auto view = snd::buildSealedSoundnessView(*artifact);
  if (!view)
    return failError(view.takeError());

  // The profile pin is what keeps a vocabulary edit from changing what a
  // fixed contract means, so it is checked rather than carried: the
  // named profile must exist in this environment and its content digest
  // must be the one the contract pinned.
  const zkc::registry::ClaimProfile *profile =
      artifact->environment().protocolVocabulary().lookupProfile(
          contract->profileName);
  if (!profile)
    return fail("the contract pins claim profile '" + contract->profileName +
                "', which this protocol vocabulary does not admit");
  if (profile->contentDigest() != contract->profileDigest)
    return fail("the contract pins claim profile '" + contract->profileName +
                "' at " + contract->profileDigest +
                ", this vocabulary admits it at " +
                profile->contentDigest().str());

  Report report;
  report.computed.push_back("claim profile '" + contract->profileName +
                            "' resolves at the pinned digest");

  // -- Step 1: the partition against the artifact's claim descriptors.
  // -- A contract that names no claim of this artifact is a refusal,
  // -- not an empty pass.
  bool matched = false;
  const std::map<std::string, std::string, std::less<>> *matchedAnchors =
      nullptr;
  for (const auto &anchors : view->claimAnchorsByIndex) {
    bool candidate = !anchors.empty();
    for (const auto &[name, value] : contract->relationAnchors) {
      auto found = anchors.find(name);
      candidate &= found != anchors.end() && found->second == value;
    }
    if (!candidate)
      continue;
    matched = true;
    matchedAnchors = &anchors;
    for (const auto &[name, value] : contract->relationAnchors) {
      report.computed.push_back("relation anchor '" + name +
                                "' equals the artifact's");
      if (value == kEmptyInputDigest)
        report.asserted.push_back(
            "relation anchor '" + name +
            "' is the digest of empty input: the scope gate it would "
            "provide is vacuous");
    }
    for (const std::string &name : contract->instanceAnchors)
      if (anchors.find(name) != anchors.end())
        report.computed.push_back("instance anchor '" + name +
                                  "' is present on the matched claim");
    break;
  }
  if (!matched)
    return fail("no claim of artifact " + view->artifactId +
                " carries the contract's relation anchors: the contract "
                "does not describe this artifact");

  // -- Step 2: the bytes, when supplied and the format has a reader.
  std::optional<zkc::relation::R1csHeader> header;
  if (!bytesFilename.empty()) {
    if (contract->format != "r1cs-bin-v1")
      return fail("format '" + contract->format +
                  "' has no reader; relation bytes cannot be read for it");
    auto buffer = MemoryBuffer::getFile(bytesFilename, /*IsText=*/false);
    if (!buffer)
      return fail("cannot read '" + bytesFilename + "'");
    StringRef bytes = (*buffer)->getBuffer();
    SHA256 hasher;
    hasher.update(bytes);
    std::string digest = "sha256:" + toHex(hasher.final(), /*LowerCase=*/true);
    report.computed.push_back("content digest of the supplied bytes is " +
                              digest);
    if (!contract->contentDigest.empty()) {
      if (contract->contentDigest != digest)
        return fail("the supplied bytes digest to " + digest +
                    ", the contract pins " + contract->contentDigest);
      report.crossChecked.push_back(
          "contract-declared content digest agrees with the byte-derived one");
    }
    auto parsed = zkc::relation::readR1csHeader(
        bytes, contract->instanceEncoding.fieldOrder);
    if (!parsed)
      return failError(parsed.takeError());
    header = *parsed;
    report.computed.push_back("header prime " + header->prime);
    report.computed.push_back("header public arity " +
                              std::to_string(header->publicArity));
    report.computed.push_back("header private-input count " +
                              std::to_string(header->privateInputs));
    report.computed.push_back("header constraint count " +
                              std::to_string(header->constraintCount));
  }

  // -- Step 3: every cross-check whose two sides are present.
  const zkc::registry::InstanceEncoding &encoding = contract->instanceEncoding;
  if (header) {
    if (encoding.kind == zkc::registry::InstanceEncodingKind::FieldVector) {
      if (encoding.arity != header->publicArity)
        return fail("declared arity " + std::to_string(encoding.arity) +
                    " disagrees with the header's public arity " +
                    std::to_string(header->publicArity));
      report.crossChecked.push_back(
          "contract-declared arity agrees with the byte-derived one");
      if (encoding.fieldOrder != header->prime)
        return fail("declared field order " + encoding.fieldOrder +
                    " disagrees with the header prime " + header->prime);
      report.crossChecked.push_back(
          "contract-declared field order agrees with the header prime");
    }
    if (!contract->witnessPorts.opaque) {
      int64_t declared = 0;
      for (const auto &port : contract->witnessPorts.ports)
        declared += port.count;
      if (declared != header->privateInputs)
        return fail("declared witness-port total " + std::to_string(declared) +
                    " disagrees with the header's private-input count " +
                    std::to_string(header->privateInputs));
      report.crossChecked.push_back(
          "contract-declared witness-port total agrees with the byte-derived "
          "private-input count");
    }
    if (contract->constraintCount) {
      if (*contract->constraintCount != header->constraintCount)
        return fail("declared constraint count " +
                    std::to_string(*contract->constraintCount) +
                    " disagrees with the header's " +
                    std::to_string(header->constraintCount));
      report.crossChecked.push_back(
          "contract-declared constraint count agrees with the byte-derived "
          "one");
    }
  }

  // The correspondence against the artifact's own statement ABI.
  for (const auto &entry : contract->correspondence) {
    if (!is_contained(view->statementLabels, entry.label))
      return fail("correspondence slot " + std::to_string(entry.slot) +
                  " names statement label '" + entry.label +
                  "', which the artifact's ABI does not carry");
    report.computed.push_back("statement label '" + entry.label +
                              "' is in the artifact's ABI");
  }
  // Labels the correspondence does not name stay protocol-only; saying
  // so keeps a reader from inferring the relation covers them.
  for (const std::string &label : view->statementLabels) {
    bool covered = false;
    for (const auto &entry : contract->correspondence)
      covered |= entry.label == label;
    if (!covered)
      report.computed.push_back("statement label '" + label +
                                "' is protocol-only: no relation slot "
                                "corresponds to it");
  }

  // The declared field against the field a derivation over this
  // artifact declares — a compatibility relation, never equality with a
  // challenge space, which is a strict subset of the field by design.
  if (!fieldOrder.empty() &&
      encoding.kind == zkc::registry::InstanceEncodingKind::FieldVector) {
    if (fieldOrder != encoding.fieldOrder)
      return fail("the expected field " + fieldOrder +
                  " disagrees with the contract's instance field " +
                  encoding.fieldOrder);
    // Named for what it is: this side is the caller's, not a fact read
    // out of a derivation. Reading the analysis parameter from the
    // artifact's own derivations is the specified form and is recorded
    // as a gap, so the label may not claim it here.
    report.crossChecked.push_back(
        "contract-declared field agrees with the caller-supplied expected "
        "field");
  }

  // Sealed material bindings covering a contract anchor: where one
  // exists, the bound value's label must appear in the correspondence,
  // and a binding that contradicts the wiring refuses. Instance anchors
  // are included deliberately — a statement anchor is exactly where a
  // sealed binding grounds the instance.
  std::map<std::string, std::string, std::less<>> contractAnchors =
      contract->relationAnchors;
  if (matchedAnchors)
    for (const std::string &name : contract->instanceAnchors) {
      auto found = matchedAnchors->find(name);
      if (found != matchedAnchors->end())
        contractAnchors[name] = found->second;
    }
  for (const auto &[name, value] : contractAnchors) {
    if (!view->boundMaterialRefs.count(value))
      continue;
    auto label = view->boundMaterialLabels.find(value);
    if (label == view->boundMaterialLabels.end()) {
      report.computed.push_back("anchor '" + name +
                                "' is materially bound to an unlabelled "
                                "value");
      continue;
    }
    bool wired = false;
    for (const auto &entry : contract->correspondence)
      wired |= entry.label == label->second;
    if (!wired)
      return fail("a sealed material binding grounds anchor '" + name +
                  "' in statement value '" + label->second +
                  "', which the correspondence does not wire");
    report.crossChecked.push_back(
        "a sealed material binding grounds anchor '" + name +
        "' in statement value '" + label->second +
        "', which the correspondence wires");
  }

  // -- Step 4: the asserted remainder, always named.
  if (contract->attestedOnly())
    report.asserted.push_back(
        "identity is attested only: '" + contract->attestor +
        "' asserts this identifier denotes the relation; zkc computed no "
        "digest over its bytes");
  if (!bytesFilename.empty())
    report.asserted.push_back(
        "that the supplied bytes are the relation the anchors name: no "
        "anchor-preimage rule exists, so the connection is declaration");
  if (!header && contract->format != "opaque")
    report.asserted.push_back(
        "every interface fact this contract declares: no bytes were "
        "supplied, so nothing was read");
  report.asserted.push_back(
      "what each statement slot means (zkc.assume."
      "statement_correspondence_wiring)");
  report.asserted.push_back(
      "that the relation is not underconstrained, that its witness "
      "generator is correct, and the provenance of its bytes");
  if (contract->constraintCount)
    report.asserted.push_back(
        header ? "that the constraint count agreeing with the supplied "
                 "bytes is the count of the relation the anchors name "
                 "(zkc.assume.constraint_count_matches_relation, reduced "
                 "to the bytes-to-anchors gap)"
               : "the declared constraint count (zkc.assume."
                 "constraint_count_matches_relation)");

  json::Array computed, crossChecked, asserted;
  for (const std::string &line : report.computed)
    computed.push_back(line);
  for (const std::string &line : report.crossChecked)
    crossChecked.push_back(line);
  for (const std::string &line : report.asserted)
    asserted.push_back(line);
  json::Object out{{"artifact", view->artifactId},
                   {"asserted", std::move(asserted)},
                   {"contract_digest", contract->digest},
                   {"cross_checked", std::move(crossChecked)},
                   {"computed", std::move(computed)}};
  if (Error err = zkc::encoding::writeCanonicalJson(json::Value(std::move(out)),
                                                    outs()))
    return failError(std::move(err));
  outs() << "\n";
  return 0;
}
