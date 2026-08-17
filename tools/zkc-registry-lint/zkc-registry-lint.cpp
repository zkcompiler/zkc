//===- zkc-registry-lint.cpp - Registry file validation ---------*- C++ -*-===//
// Validates a registry JSON file under the registry loading discipline
// (RegistryFile; carrier.md §7) and, on success, prints the registered
// entries in canonical JSON form — the same bytes a reference model
// prints for its seed table, so the two can be diffed. The registry
// kind is dispatched on the file's own "registry" field.
//===----------------------------------------------------------------------===//

#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Registry/RegistryFile.h"
#include "zkc/Registry/RelationContractRegistry.h"
#include "zkc/Soundness/SignatureEncoding.h"
#include "zkc/Soundness/SignatureFile.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<registry.json>"));
static int fail(Error err) { return zkc::tool::reportRefusal(std::move(err)); }

static int emit(json::Value value) {
  if (Error err = zkc::encoding::writeCanonicalJson(value, outs()))
    return fail(std::move(err));
  return 0;
}

static int lintProtocolVocabulary(StringRef json, StringRef source) {
  auto registry = zkc::registry::ProtocolVocabulary::parse(json, source);
  if (!registry)
    return fail(registry.takeError());
  return emit(registry->toCanonicalJson());
}

static int lintConstructionProfiles(StringRef json, StringRef source) {
  auto registry =
      zkc::registry::ConstructionProfileRegistry::parse(json, source);
  if (!registry)
    return fail(registry.takeError());
  json::Object sponges, codecs;
  for (const auto &[name, sponge] : registry->entries())
    sponges[name] = sponge.toCanonicalJson();
  for (const auto &[name, codec] : registry->codecEntries())
    codecs[name] = codec.toCanonicalJson();
  return emit(json::Object{{"codecs", std::move(codecs)},
                           {"sponges", std::move(sponges)}});
}

static int lintRelationContracts(StringRef json, StringRef source) {
  auto registry = zkc::registry::RelationContractRegistry::parse(json, source);
  if (!registry)
    return fail(registry.takeError());
  json::Object contracts, revisions;
  for (const auto &[name, contract] : registry->entries()) {
    contracts[name] = contract.toCanonicalJson();
    // The entry digest is what a judgment cites; the map key above is
    // a lookup handle and is not covered by it
    // (docs/spec/relations.md §1).
    revisions[name] = contract.digest;
  }
  return emit(json::Object{{"contracts", std::move(contracts)},
                           {"digests", std::move(revisions)}});
}

static int lintSoundnessSignature(StringRef json, StringRef source) {
  auto signature = zkc::soundness::parseSignature(json, source);
  if (!signature)
    return fail(signature.takeError());
  json::Object rules, bindings, ruleRevisions, bindingRevisions;
  for (const auto &[id, rule] : signature->catalog.rules) {
    rules[id] = zkc::soundness::encodeRuleDocument(rule);
    // The document is the digest preimage, so printing the digest beside it
    // states the content address a second implementation has to reach from
    // the same bytes. A rule no binding names has no other place to appear.
    auto revision = zkc::soundness::ruleDigest(rule);
    if (!revision)
      return fail(revision.takeError());
    ruleRevisions[id] = *revision;
  }
  for (const auto &[id, binding] : signature->catalog.bindings) {
    bindings[id] = zkc::soundness::encodeBindingDocument(binding);
    auto revision = zkc::soundness::bindingDigest(binding);
    if (!revision)
      return fail(revision.takeError());
    bindingRevisions[id] = *revision;
  }
  auto digest = zkc::soundness::signatureDigest(signature->catalog);
  if (!digest)
    return fail(digest.takeError());
  return emit(json::Object{
      {"bindings", std::move(bindings)},
      {"digest", *digest},
      {"revisions", json::Object{{"bindings", std::move(bindingRevisions)},
                                 {"rules", std::move(ruleRevisions)}}},
      {"rules", std::move(rules)},
      {"schemas", zkc::soundness::encodeSchemaContextDocument(
                      signature->catalog.schemas)}});
}

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv, "zkc-registry-lint: validate a zkc registry file\n");

  // The only path in this tool that never reaches its subject: every
  // other exit is the admission judgment this tool exists to make.
  auto buffer = zkc::registry::RegistryFile::readFile(inputFilename);
  if (!buffer)
    return zkc::tool::reportCannotAnswer(llvm::Twine("[zkc-E900] ") + llvm::toString(buffer.takeError()));
  StringRef json = (*buffer)->getBuffer();

  // Dispatch on the file's own name field; the chosen loader
  // re-validates the envelope fail-closed.
  // The peek reads one field to choose a loader, and the loader it
  // chooses re-parses under the uniqueness scan; running that scan here
  // too would read the file twice to learn nothing twice.
  std::string name;
  if (Expected<json::Value> peek = json::parse(json)) {
    if (const json::Object *root = peek->getAsObject())
      name = root->getString("registry").value_or("").str();
  } else {
    // Every diagnostic names its file, syntax errors included.
    return fail(
        createStringError(inputFilename + ": " + toString(peek.takeError())));
  }
  if (name == "zkc.protocol_vocabulary")
    return lintProtocolVocabulary(json, inputFilename);
  if (name == "zkc.construction_profiles")
    return lintConstructionProfiles(json, inputFilename);
  if (name == "zkc.soundness_signature")
    return lintSoundnessSignature(json, inputFilename);
  if (name == "zkc.relation_contract")
    return lintRelationContracts(json, inputFilename);
  return fail(createStringError("unknown registry '" + name +
                                "' (this lint knows zkc.protocol_vocabulary, "
                                "zkc.construction_profiles, "
                                "zkc.soundness_signature, and "
                                "zkc.relation_contract)"));
}
