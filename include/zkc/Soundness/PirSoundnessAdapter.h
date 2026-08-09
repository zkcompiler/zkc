//===- PirSoundnessAdapter.h - PIR to owned soundness view ------*- C++ -*-===//
#ifndef ZKC_SOUNDNESS_PIRSOUNDNESSADAPTER_H
#define ZKC_SOUNDNESS_PIRSOUNDNESSADAPTER_H

#include "zkc/Soundness/SealedSoundnessView.h"
#include "llvm/Support/Error.h"

namespace zkc::artifact {
class AdmittedPirArtifact;
} // namespace zkc::artifact

namespace zkc::soundness {

/// Project an admitted PIR artifact into an MLIR-free owned soundness view.
/// Admission has already established transport identity and the exact
/// registry-backed seal judgment. This adapter applies only the additional
/// soundness-specific judgments to an independent internal clone. The returned
/// value retains no operation, value, attribute, StringRef, or registry
/// pointer. This bare aggregate is the trusted input of the low-level
/// representation-neutral evaluator.
llvm::Expected<SealedSoundnessView>
buildSealedSoundnessView(const artifact::AdmittedPirArtifact &artifact);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_PIRSOUNDNESSADAPTER_H
