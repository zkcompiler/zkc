//===- ProtocolEnvironment.h - protocol semantic authorities ---*- C++ -*-===//
#ifndef ZKC_REGISTRY_PROTOCOLENVIRONMENT_H
#define ZKC_REGISTRY_PROTOCOLENVIRONMENT_H

#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <memory>
#include <optional>

namespace zkc::registry {

/// The immutable authority bundle used to judge one protocol.
///
/// Artifact identity cites only the entries a protocol consumes.  The complete
/// compiler-configuration preimage is a separate use of the same authorities;
/// it deliberately includes every entry a compiler provider may consult.
class ProtocolEnvironment {
public:
  ProtocolEnvironment(ProtocolVocabulary vocabulary,
                      std::optional<ConstructionProfileRegistry>
                          constructionProfiles = std::nullopt);

  static llvm::Expected<ProtocolEnvironment>
  loadFromFiles(llvm::StringRef protocolVocabularyPath,
                llvm::StringRef constructionProfilePath = {});

  const ProtocolVocabulary &protocolVocabulary() const {
    return *protocolVocabulary_;
  }

  const ConstructionProfileRegistry *constructionProfiles() const {
    return constructionProfiles_.get();
  }

  /// The normalized, complete authority preimage for compiler configuration
  /// identity.  This is not an artifact identity and must not be substituted
  /// for the exact cited closure stamped by sealing.
  llvm::json::Value compilerConfiguration() const;

private:
  std::shared_ptr<const ProtocolVocabulary> protocolVocabulary_;
  std::shared_ptr<const ConstructionProfileRegistry> constructionProfiles_;
};

} // namespace zkc::registry

#endif // ZKC_REGISTRY_PROTOCOLENVIRONMENT_H
