//===- ProtocolEnvironment.cpp - protocol semantic authorities ----------===//

#include "zkc/Registry/ProtocolEnvironment.h"

using namespace llvm;
using namespace zkc::registry;

ProtocolEnvironment::ProtocolEnvironment(
    ProtocolVocabulary vocabulary,
    std::optional<ConstructionProfileRegistry> constructionProfiles)
    : protocolVocabulary_(
          std::make_shared<const ProtocolVocabulary>(std::move(vocabulary))) {
  if (constructionProfiles)
    constructionProfiles_ = std::make_shared<const ConstructionProfileRegistry>(
        std::move(*constructionProfiles));
}

Expected<ProtocolEnvironment>
ProtocolEnvironment::loadFromFiles(StringRef protocolVocabularyPath,
                                   StringRef constructionProfilePath) {
  if (protocolVocabularyPath.empty())
    return createStringError("a protocol-vocabulary path is required");

  auto vocabulary = ProtocolVocabulary::loadFromFile(protocolVocabularyPath);
  if (!vocabulary)
    return vocabulary.takeError();

  std::optional<ConstructionProfileRegistry> constructionProfiles;
  if (!constructionProfilePath.empty()) {
    auto loaded =
        ConstructionProfileRegistry::loadFromFile(constructionProfilePath);
    if (!loaded)
      return loaded.takeError();
    constructionProfiles = std::move(*loaded);
  }
  return ProtocolEnvironment(std::move(*vocabulary),
                             std::move(constructionProfiles));
}

json::Value ProtocolEnvironment::compilerConfiguration() const {
  json::Object construction;
  if (constructionProfiles_) {
    json::Object sponges;
    for (const auto &[name, profile] : constructionProfiles_->entries())
      sponges[name] = profile.toCanonicalJson();
    json::Object codecs;
    for (const auto &[name, profile] : constructionProfiles_->codecEntries())
      codecs[name] = profile.toCanonicalJson();
    construction = json::Object{{"codecs", std::move(codecs)},
                                {"registry", "zkc.construction_profiles"},
                                {"sponges", std::move(sponges)}};
  }

  json::Object configuration{
      {"protocol_vocabulary", protocolVocabulary_->toCanonicalJson()}};
  if (constructionProfiles_)
    configuration["construction_profiles"] = std::move(construction);
  else
    configuration["construction_profiles"] = nullptr;
  return configuration;
}
