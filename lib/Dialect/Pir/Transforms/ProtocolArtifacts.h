//===- ProtocolArtifacts.h - internal admitted PIR boundaries --*- C++ -*-===//
//
// Small reusable boundaries needed by semantic transform providers: reopen an
// admitted artifact and observe verifier proof reads from admitted PIR. These
// APIs do not price codecs and contain no toy width table; they return exact
// codec references for the compiler's independent objective profile.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_LIB_DIALECT_PIR_TRANSFORMS_PROTOCOLARTIFACTS_H
#define ZKC_LIB_DIALECT_PIR_TRANSFORMS_PROTOCOLARTIFACTS_H

#include "Artifact/ArtifactInternal.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <string>
#include <vector>

namespace zkc::pir {

struct VerifierProofReadObservation {
  uint64_t eventPosition = 0;
  std::string payloadClass;
  std::string codecId;
  std::string codecDigest;
  uint64_t count = 1;
};

bool operator==(const VerifierProofReadObservation &left,
                const VerifierProofReadObservation &right);

/// Clone an admitted artifact and reopen its semantic body for a transform.
/// The returned owner contains the original sealed root and one open protocol
/// immediately after it. Resolved vocabulary and discardable metadata are not
/// copied: sealing the transformed result resolves authority afresh.
llvm::Expected<artifact::detail::MutablePirArtifact>
openAdmittedProtocolForTransform(const artifact::AdmittedPirArtifact &artifact);

/// Derive exact proof-stream reads from admitted PIR source semantics. Every
/// pir.slot contributes one read, in canonical event order, with the codec
/// content digest pinned by the sealed vocabulary.
llvm::Expected<std::vector<VerifierProofReadObservation>>
deriveVerifierProofReads(const artifact::AdmittedPirArtifact &artifact);

} // namespace zkc::pir

#endif // ZKC_LIB_DIALECT_PIR_TRANSFORMS_PROTOCOLARTIFACTS_H
