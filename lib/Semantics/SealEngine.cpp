//===- SealEngine.cpp - one protocol seal implementation ----------------===//

#include "zkc/Semantics/SealEngine.h"

#include "ConstructionGraph.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Pir/KappaView.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Semantics/SealBattery.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {

template <typename DigestLookup>
FailureOr<DictionaryAttr> resolveSection(Operation *container,
                                         ArrayRef<StringRef> citations,
                                         DigestLookup digestOf) {
  SmallVector<NamedAttribute> entries;
  for (StringRef id : citations) {
    std::optional<StringRef> digest = digestOf(id);
    if (!digest) {
      container->emitOpError()
          << "cited id '" << id
          << "' passed the seal battery but has no exact content digest";
      return failure();
    }
    entries.push_back({StringAttr::get(container->getContext(), id),
                       StringAttr::get(container->getContext(), *digest)});
  }
  return DictionaryAttr::get(container->getContext(), entries);
}

FailureOr<DictionaryAttr>
buildResolvedVocabulary(pir::ProtocolOp protocol,
                        const registry::ProtocolEnvironment &environment,
                        const semantics::ConstructionGraph &routes) {
  const registry::ProtocolVocabulary &vocabulary =
      environment.protocolVocabulary();
  pir::ProtocolVocabularyCitations cited = pir::collectCitedProtocolVocabulary(
      protocol.getBody().front(), vocabulary);

  auto claimProfiles = resolveSection(
      protocol, cited.claimProfiles,
      [&](StringRef id) -> std::optional<StringRef> {
        const auto *entry = vocabulary.lookupProfile(id);
        return entry ? std::optional<StringRef>(entry->contentDigest())
                     : std::nullopt;
      });
  auto checkContracts = resolveSection(
      protocol, cited.checkContracts,
      [&](StringRef id) -> std::optional<StringRef> {
        const auto *entry = vocabulary.lookupCheckContract(id);
        return entry ? std::optional<StringRef>(entry->contentDigest())
                     : std::nullopt;
      });
  auto reductionContracts = resolveSection(
      protocol, cited.reductionContracts,
      [&](StringRef id) -> std::optional<StringRef> {
        const auto *entry = vocabulary.lookupReductionContract(id);
        return entry ? std::optional<StringRef>(entry->contentDigest())
                     : std::nullopt;
      });
  auto terminalRules = resolveSection(
      protocol, cited.terminalRules,
      [&](StringRef id) -> std::optional<StringRef> {
        const auto *entry = vocabulary.lookupRule(id);
        return entry ? std::optional<StringRef>(entry->contentDigest())
                     : std::nullopt;
      });
  if (failed(claimProfiles) || failed(checkContracts) ||
      failed(reductionContracts) || failed(terminalRules))
    return failure();

  StringRef spongeName = pir::kappaSpongeName(protocol.getKappa());
  SmallVector<std::string> constructionStorage;
  if (!spongeName.empty())
    constructionStorage.push_back(("sponge:" + spongeName).str());
  for (StringRef codecName : pir::kappaConsumedCodecNames(protocol.getKappa()))
    constructionStorage.push_back(("codec:" + codecName).str());
  llvm::sort(constructionStorage);
  constructionStorage.erase(llvm::unique(constructionStorage),
                            constructionStorage.end());
  SmallVector<StringRef> citedConstruction;
  for (const std::string &name : constructionStorage)
    citedConstruction.push_back(name);

  const registry::ConstructionProfileRegistry *profiles =
      environment.constructionProfiles();
  auto constructionProfiles = resolveSection(
      protocol, citedConstruction,
      [&](StringRef name) -> std::optional<StringRef> {
        if (!profiles)
          return std::nullopt;
        if (name.consume_front("sponge:")) {
          const auto *profile = profiles->lookup(name);
          return profile ? std::optional<StringRef>(profile->digest)
                         : std::nullopt;
        }
        if (name.consume_front("codec:")) {
          const auto *profile = profiles->lookupCodec(name);
          return profile ? std::optional<StringRef>(profile->digest)
                         : std::nullopt;
        }
        return std::nullopt;
      });
  if (failed(constructionProfiles))
    return failure();

  MLIRContext *context = protocol.getContext();
  SmallVector<NamedAttribute> sections = {
      {StringAttr::get(context, "claim_profiles"), *claimProfiles},
      {StringAttr::get(context, "check_contracts"), *checkContracts},
      {StringAttr::get(context, "reduction_contracts"), *reductionContracts},
      {StringAttr::get(context, "terminal_rules"), *terminalRules},
      {StringAttr::get(context, "construction_profiles"),
       *constructionProfiles}};
  auto valueProfiles = resolveSection(
      protocol, cited.valueProfiles,
      [&](StringRef id) -> std::optional<StringRef> {
        const auto *entry = vocabulary.lookupValueProfile(id);
        return entry ? std::optional<StringRef>(entry->contentDigest())
                     : std::nullopt;
      });
  if (failed(valueProfiles))
    return failure();
  if (!valueProfiles->empty())
    sections.push_back(
        {StringAttr::get(context, "value_profiles"), *valueProfiles});

  DictionaryAttr holeContracts = routes.resolvedHoleContracts(context);
  if (!holeContracts.empty())
    sections.push_back(
        {StringAttr::get(context, "hole_contracts"), holeContracts});
  return DictionaryAttr::get(context, sections);
}

} // namespace

FailureOr<pir::SealedOp>
semantics::SealEngine::seal(pir::ProtocolOp protocol) const {
  auto routes = detail::judgeOpenProtocol(protocol, environment_);
  if (failed(routes))
    return failure();

  auto resolvedVocabulary =
      buildResolvedVocabulary(protocol, environment_, *routes);
  if (failed(resolvedVocabulary))
    return failure();

  Attribute authoredVocabulary = protocol->getAttr("vocab");
  auto restoreAuthoredVocabulary = [&] {
    if (authoredVocabulary)
      protocol->setAttr("vocab", authoredVocabulary);
    else
      protocol->removeAttr("vocab");
  };
  protocol.setVocabAttr(*resolvedVocabulary);
  auto id = encoding::computeId(protocol.getOperation());
  if (!id) {
    restoreAuthoredVocabulary();
    protocol.emitOpError() << "cannot compute sealed identity: "
                           << toString(id.takeError());
    return failure();
  }

  OpBuilder builder(protocol);
  auto sealed = pir::SealedOp::create(
      builder, protocol.getLoc(), protocol.getProtocolName(), *id,
      protocol.getKappaAttr(), *resolvedVocabulary, protocol.getRoutesAttr(),
      protocol.getSegments(), protocol.getPolicy());
  sealed->setDiscardableAttrs(protocol->getDiscardableAttrDictionary());
  IRMapping mapping;
  protocol.getBody().cloneInto(&sealed.getBody(), mapping);
  if (failed(verify(sealed.getOperation()))) {
    sealed.erase();
    restoreAuthoredVocabulary();
    return failure();
  }

  protocol.erase();
  return sealed;
}

FailureOr<semantics::ConstructionGraph> semantics::detail::judgeOpenProtocol(
    pir::ProtocolOp protocol,
    const registry::ProtocolEnvironment &environment) {
  if (!protocol) {
    return failure();
  }
  if (failed(verify(protocol.getOperation())))
    return failure();

  const registry::ProtocolVocabulary &vocabulary =
      environment.protocolVocabulary();
  if (failed(pir::runSealBattery(
          protocol, protocol.getKappa(), protocol.getVocab(),
          protocol.getSegments(), protocol.getPolicy(), /*recheck=*/false,
          vocabulary, environment.constructionProfiles())))
    return failure();

  return ConstructionGraph::build(protocol, environment);
}

LogicalResult semantics::SealEngine::recheck(pir::SealedOp sealed) const {
  if (!sealed)
    return failure();
  if (failed(verify(sealed.getOperation())))
    return failure();

  const registry::ProtocolVocabulary &vocabulary =
      environment_.protocolVocabulary();
  if (failed(pir::runSealBattery(sealed, sealed.getKappa(), sealed.getVocab(),
                                 sealed.getSegments(), sealed.getPolicy(),
                                 /*recheck=*/true, vocabulary,
                                 environment_.constructionProfiles())))
    return failure();
  if (failed(ConstructionGraph::build(sealed, environment_)))
    return failure();

  if (Error error = encoding::validatePirIdentity(sealed.getOperation())) {
    sealed.emitOpError() << toString(std::move(error));
    return failure();
  }
  return success();
}
