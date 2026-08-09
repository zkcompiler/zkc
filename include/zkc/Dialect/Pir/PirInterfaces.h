//===- PirInterfaces.h - Protocol member interface --------------*- C++ -*-===//
#ifndef ZKC_DIALECT_PIR_PIRINTERFACES_H
#define ZKC_DIALECT_PIR_PIRINTERFACES_H

#include "mlir/IR/OpDefinition.h"

namespace zkc {
namespace pir {

/// The body layout phase of a protocol member (carrier.md §4):
/// [sources]* begin [spine events]* end [reduces]* [attachments]* [sinks]*.
enum class MemberPhase { Source, SpineEvent, Transformer, Attachment, Sink };

/// A body event's reduction membership (carrier.md §4): the owning
/// reduce instance's label, the schema role the event plays, and the
/// occurrence index for declared-multiplicity roles. The round number
/// is deliberately NOT here — role + schema reach it through the
/// registry's role→round assignment, the single declaration that also
/// prices the round (kernel.md §5.2).
struct Membership {
  llvm::StringRef instance;
  llvm::StringRef role;
  int64_t idx;
};

} // namespace pir
} // namespace zkc

#include "zkc/Dialect/Pir/PirInterfaces.h.inc"

namespace zkc {
namespace pir {

/// Verify the protocol-neutral challenge-capability contract shared by every
/// implementing op: the interface identifies one exact result owned by the
/// op, and that result is a `!pir.val` whose semantic class equals the class
/// reported by the interface.  Container verification calls this generically;
/// individual implementing ops may call it from their own verifier too.
mlir::LogicalResult
verifyChallengeCapability(ChallengeCapabilityOpInterface capability);

} // namespace pir
} // namespace zkc

#endif // ZKC_DIALECT_PIR_PIRINTERFACES_H
