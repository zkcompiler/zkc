//===- ProtocolArtifacts.cpp - in-memory PIR core boundaries ---*- C++ -*-===//

#include "ProtocolArtifacts.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Pir/KappaView.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ProtocolEnvironment.h"

using namespace mlir;

namespace {

llvm::Expected<std::pair<std::string, std::string>>
resolveCodec(llvm::StringRef payloadClass, llvm::StringRef codecId,
             std::optional<DictionaryAttr> sealedVocabulary,
             const zkc::registry::ConstructionProfileRegistry &profiles) {
  if (codecId.empty())
    return llvm::createStringError("no codec for proof-read payload class '" +
                                   payloadClass + "'");
  const zkc::registry::CodecProfile *codec = profiles.lookupCodec(codecId);
  if (!codec || !zkc::encoding::isSha256Ref(codec->digest))
    return llvm::createStringError("proof-read codec '" + codecId +
                                   "' has no exact construction-profile "
                                   "entry");

  // Sealed PIR pins the registry content consumed to interpret the codec id.
  // Require that pin rather than silently accepting environmental resolution.
  if (sealedVocabulary) {
    auto sectionEntry = sealedVocabulary->getNamed("construction_profiles");
    auto section = sectionEntry
                       ? dyn_cast<DictionaryAttr>(sectionEntry->getValue())
                       : DictionaryAttr();
    std::string key = ("codec:" + codecId).str();
    auto pinnedEntry = section ? section.getNamed(key) : std::nullopt;
    auto pinned = pinnedEntry ? dyn_cast<StringAttr>(pinnedEntry->getValue())
                              : StringAttr();
    if (!pinned || pinned.getValue() != codec->digest)
      return llvm::createStringError(
          "sealed vocabulary does not pin the exact proof-read codec '" +
          codecId + "'");
  }
  return std::make_pair(codecId.str(), codec->digest);
}

} // namespace

bool zkc::pir::operator==(const VerifierProofReadObservation &left,
                          const VerifierProofReadObservation &right) {
  return left.eventPosition == right.eventPosition &&
         left.payloadClass == right.payloadClass &&
         left.codecId == right.codecId &&
         left.codecDigest == right.codecDigest && left.count == right.count;
}

llvm::Expected<zkc::artifact::detail::MutablePirArtifact>
zkc::pir::openAdmittedProtocolForTransform(
    const artifact::AdmittedPirArtifact &artifact) {
  artifact::detail::MutablePirArtifact result =
      artifact::detail::ArtifactAccess::cloneForReopen(artifact);
  SealedOp sealed = result.sealed();

  OpBuilder builder(sealed);
  builder.setInsertionPointAfter(sealed);
  auto protocol = ProtocolOp::create(
      builder, sealed.getLoc(), sealed.getProtocolName(), sealed.getKappaAttr(),
      // Resolved authority belongs to the next seal, not the editable clone.
      /*vocab=*/DictionaryAttr(), sealed.getRoutesAttr(), sealed.getSegments(),
      sealed.getPolicy());
  IRMapping mapping;
  sealed.getBody().cloneInto(&protocol.getBody(), mapping);
  if (failed(verify(protocol.getOperation()))) {
    protocol.erase();
    return llvm::createStringError(
        "authenticated pir.sealed body did not clone to valid open PIR");
  }
  return std::move(result);
}

llvm::Expected<std::vector<zkc::pir::VerifierProofReadObservation>>
zkc::pir::deriveVerifierProofReads(
    const artifact::AdmittedPirArtifact &artifact) {
  const registry::ConstructionProfileRegistry *profiles =
      artifact.environment().constructionProfiles();
  if (!profiles)
    return llvm::createStringError(
        "admitted PIR environment has no construction profiles");
  artifact::detail::MutablePirArtifact clone =
      artifact::detail::ArtifactAccess::cloneForReopen(artifact);
  SealedOp sealed = clone.sealed();
  auto canonical = encoding::canonicalIndex(sealed.getOperation());
  if (!canonical)
    return canonical.takeError();

  std::vector<VerifierProofReadObservation> result;
  for (auto slot : sealed.getBody().front().getOps<SlotOp>()) {
    auto event = canonical->eventPositions.find(slot.getVal());
    if (event == canonical->eventPositions.end() || event->second < 0)
      return llvm::createStringError(
          "sealed proof slot has no canonical event position");
    auto codec =
        resolveCodec(slot.getPayloadClass(),
                     kappaCodecName(sealed.getKappa(), slot.getPayloadClass()),
                     sealed.getVocab(), *profiles);
    if (!codec)
      return codec.takeError();
    result.push_back({static_cast<uint64_t>(event->second),
                      slot.getPayloadClass().str(), std::move(codec->first),
                      std::move(codec->second), 1});
  }
  return result;
}
