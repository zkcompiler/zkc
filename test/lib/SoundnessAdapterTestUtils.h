//===- SoundnessAdapterTestUtils.h - admitted PIR test fixtures -*- C++ -*-===//
#ifndef ZKC_TEST_SOUNDNESSADAPTERTESTUTILS_H
#define ZKC_TEST_SOUNDNESSADAPTERTESTUTILS_H

#include "zkc/Artifact/Artifact.h"
#include "zkc/Registry/ProtocolEnvironment.h"

namespace zkc::test {

/// Snapshot a test pass's sealed fixture and admit the independent artifact
/// against the same authorities supplied to the production tools.
inline llvm::Expected<artifact::AdmittedPirArtifact>
admitSoundnessFixture(pir::SealedOp sealed,
                      llvm::StringRef protocolVocabularyPath,
                      llvm::StringRef constructionProfilePath) {
  auto environment = registry::ProtocolEnvironment::loadFromFiles(
      protocolVocabularyPath, constructionProfilePath);
  if (!environment)
    return environment.takeError();
  auto decoded = artifact::snapshotArtifact(sealed);
  if (!decoded)
    return decoded.takeError();
  return artifact::admitArtifact(std::move(*decoded), std::move(*environment));
}

} // namespace zkc::test

#endif // ZKC_TEST_SOUNDNESSADAPTERTESTUTILS_H
