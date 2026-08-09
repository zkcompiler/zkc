//===- TranscriptSchedule.cpp - derived transcript schedule -----*- C++ -*-===//

#include "zkc/Dialect/Oir/TranscriptSchedule.h"

#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;

namespace zkc {
namespace oir {
namespace {

static llvm::Expected<std::string> codecFor(DictionaryAttr codecs,
                                            llvm::StringRef payloadClass) {
  if (!codecs)
    return llvm::createStringError("projected program carries no codec map");
  auto entry = codecs.getNamed(payloadClass);
  if (!entry)
    return llvm::createStringError(
        "projected program has no codec for class '" + payloadClass + "'");
  auto name = dyn_cast<StringAttr>(entry->getValue());
  if (!name || name.getValue().empty())
    return llvm::createStringError("projected codec route for class '" +
                                   payloadClass +
                                   "' is not a non-empty string");
  return name.getValue().str();
}

static llvm::Expected<llvm::SmallVector<int64_t, 1>>
sourcePositions(Operation *op) {
  llvm::SmallVector<int64_t, 1> result;
  auto src = op->getAttrOfType<ArrayAttr>("src");
  if (!src)
    return result;
  for (Attribute value : src) {
    auto position = dyn_cast<IntegerAttr>(value);
    if (!position || position.getInt() < 0)
      return llvm::createStringError(
          "transcript event carries an invalid source position");
    result.push_back(position.getInt());
  }
  return result;
}

} // namespace

llvm::Expected<TranscriptSchedule>
extractTranscriptSchedule(ArtifactOp artifact) {
  if (llvm::Error error = zkc::encoding::validateOirIdentity(artifact))
    return std::move(error);
  // The sponge chase below terminates on the verifier frame (decide); a
  // prover skeleton's stream ends in finish and has no schedule in this
  // view's vocabulary.
  if (artifact.getEndpointKind() != kEndpointVerifier)
    return llvm::createStringError(
        "transcript schedule is a verifier view; endpoint kind '%s' has no "
        "schedule here",
        artifact.getEndpointKind().str().c_str());

  ProgramOp program = *artifact.getBody().getOps<ProgramOp>().begin();
  DictionaryAttr codecs = program.getCodecs().value_or(DictionaryAttr());

  TranscriptSchedule schedule;
  schedule.artifactId = artifact.getId().str();
  schedule.source = artifact.getSource().str();
  schedule.endpointKind = artifact.getEndpointKind().str();

  TranscriptInitOp init;
  int64_t transcriptEventCount = 0;
  for (Operation &operation : program.getBody().front()) {
    if (auto candidate = dyn_cast<TranscriptInitOp>(operation)) {
      if (init)
        return llvm::createStringError(
            "projected program contains more than one transcript init");
      init = candidate;
    }
    transcriptEventCount += isa<AbsorbOp, SqueezeOp>(operation);
  }
  if (!init)
    return llvm::createStringError(
        "projected program contains no transcript init");
  schedule.sponge = init.getSponge().str();
  schedule.iv = init.getIv().str();

  // Follow the linear sponge value, rather than relying on textual operation
  // order. Verified single-block OIR makes the two orders coincide, but the
  // SSA walk is the semantic reason they do and fails closed on a fork or an
  // alien sponge consumer even when called before a whole-module verifier.
  Value sponge = init.getOut();
  int64_t index = 0;
  while (true) {
    if (!sponge.hasOneUse())
      return llvm::createStringError(
          "projected transcript sponge is not consumed exactly once");
    Operation *consumer = *sponge.getUsers().begin();
    if (auto absorb = dyn_cast<AbsorbOp>(consumer)) {
      auto type = dyn_cast<ValType>(absorb.getValue().getType());
      if (!type)
        return llvm::createStringError(
            "transcript absorb operand is not an OIR value");
      auto codec = codecFor(codecs, type.getValueClass());
      if (!codec)
        return codec.takeError();
      auto positions = sourcePositions(absorb);
      if (!positions)
        return positions.takeError();
      schedule.events.push_back(
          TranscriptAbsorb{index++, type.getValueClass().str(),
                           std::move(*codec), std::move(*positions)});
      sponge = absorb.getOut();
      continue;
    }
    if (auto squeeze = dyn_cast<SqueezeOp>(consumer)) {
      auto type = dyn_cast<ValType>(squeeze.getVal().getType());
      if (!type)
        return llvm::createStringError(
            "transcript squeeze result is not an OIR value");
      auto codec = codecFor(codecs, type.getValueClass());
      if (!codec)
        return codec.takeError();
      auto positions = sourcePositions(squeeze);
      if (!positions)
        return positions.takeError();
      schedule.events.push_back(TranscriptSqueeze{
          index++, squeeze.getLabel().str(), type.getValueClass().str(),
          std::move(*codec), squeeze.getDomain().str(), squeeze.getRule().str(),
          squeeze.getSpace().str(), squeeze.getCount().str(),
          std::move(*positions)});
      sponge = squeeze.getOut();
      continue;
    }
    if (isa<DecideOp>(consumer))
      break;
    return llvm::createStringError(
        "projected transcript sponge reaches an unknown consumer '" +
        consumer->getName().getStringRef() + "'");
  }
  if (index != transcriptEventCount)
    return llvm::createStringError(
        "projected program contains a transcript event outside the linear "
        "sponge chain");
  return schedule;
}

} // namespace oir
} // namespace zkc
