//===- TranscriptSchedule.h - derived transcript schedule -------*- C++ -*-===//
//
// A transcript schedule is a read-only view of one projected OIR artifact.
// It is deliberately smaller than an executor: the view records the ordered
// absorb/squeeze effects and their typed codec routes, but neither applies a
// sponge permutation nor manufactures challenge values.
//
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_OIR_TRANSCRIPTSCHEDULE_H
#define ZKC_DIALECT_OIR_TRANSCRIPTSCHEDULE_H

#include "zkc/Dialect/Oir/OirOps.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <string>
#include <variant>

namespace zkc {
namespace oir {

/// One transcript absorption in projected execution order. `payloadClass`
/// selects `codec` through the program's baked codec map. Source positions are
/// projection provenance, not an alternative ordering authority.
struct TranscriptAbsorb {
  int64_t index = 0;
  std::string payloadClass;
  std::string codec;
  llvm::SmallVector<int64_t, 1> sourcePositions;
};

/// One projected counted squeeze. `count == "1"` is scalar; a canonical
/// decimal in [2, 2^20] is a vector capability. `domain`, `rule`, and `space`
/// are declarations consumed by an executor or conformance checker, not
/// evidence that this view executed them.
struct TranscriptSqueeze {
  int64_t index = 0;
  std::string label;
  std::string payloadClass;
  std::string codec;
  std::string domain;
  std::string rule;
  std::string space;
  std::string count;
  llvm::SmallVector<int64_t, 1> sourcePositions;
};

using TranscriptScheduleEvent =
    std::variant<TranscriptAbsorb, TranscriptSqueeze>;

/// The transcript projection of exactly one OIR artifact. The event vector is
/// ordered by the artifact's linear SSA sponge chain (equivalently, program
/// order for a verified single-block OIR program).
struct TranscriptSchedule {
  std::string artifactId;
  std::string source;
  std::string endpointKind;
  std::string sponge;
  std::string iv;
  llvm::SmallVector<TranscriptScheduleEvent, 8> events;
};

/// Derive the schedule from typed OIR operations. The boundary first
/// authenticates the stored OIR id against the canonical program bytes.
/// Missing codec routes then fail closed: reporting an absorb or squeeze with
/// an invented/default codec would make the view weaker than the projected
/// artifact.
llvm::Expected<TranscriptSchedule>
extractTranscriptSchedule(ArtifactOp artifact);

} // namespace oir
} // namespace zkc

#endif // ZKC_DIALECT_OIR_TRANSCRIPTSCHEDULE_H
