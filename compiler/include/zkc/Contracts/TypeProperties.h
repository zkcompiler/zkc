#ifndef ZKC_CONTRACTS_TYPE_PROPERTIES_H
#define ZKC_CONTRACTS_TYPE_PROPERTIES_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"

namespace zkc::protocol {
// Classification of an admitted nominal type spelling. Formation and installed
// domain checks remain with admission and the binding registry.
inline llvm::StringRef typeKind(llvm::StringRef type) {
  return type.take_front(type.find_first_of(":<@"));
}
// Native protocol ports admit copyable aggregates recursively.
// This is a logical boundary rule, independent of representation and
// codec availability. The caller supplies a formed, depth-bounded type.
bool programPort(const BoundType &type);
// The catalog's field_array frame over `field`: an aggregate frame row.
// Encoding stays separate from formation: an array over another field is a
// valid logical type without a message frame.
bool nativeFieldArrayFrame(llvm::StringRef field);
// A canonical applied field_array representation over `field` admitting
// `size` elements: its value bytes are the field's array frame.
bool nativeFieldArrayRepresentation(llvm::StringRef field, uint64_t size,
                                    llvm::StringRef representation);
// Native arrays have a frame determined by their complete type. This
// profile fact does not install a codec in older artifact formats.
bool nativeMessageData(const BoundType &type);
bool nativeFieldArrayWire(const BoundType &type, bool physical = false);
// Complete closed native message grammar. Local copy permission alone is
// insufficient: keys, setup handles and unsupported leaves stay local.
// Atomic profile lookup is also used by native MLIR structural inspection.
// An atom is a catalog message constructor whose instance has a framed
// codec. The caller must establish nominal formation; this installs no codec
// and grants no handler.
bool nativeMessageAtom(llvm::StringRef kind, llvm::StringRef identity);
// An installation representation row of the instance whose value bytes are the
// instance's codec frame.
bool canonicalRepresentation(llvm::StringRef kind, llvm::StringRef identity,
                             llvm::StringRef representation);
// The instance's resident representation: its one nondefault installation row
// whose value bytes are the codec frame, or empty.
llvm::StringRef residentRepresentation(llvm::StringRef kind,
                                       llvm::StringRef identity);
// A commitment domain whose declared scheme requires an authorized setup.
bool setupCommitment(llvm::StringRef identity);
// Frames introduced by the structured message profile, including standalone
// numeric collections. Existing scalar and fixed-array frames keep their IDs.
inline bool nativeDataFrame(const BoundType &type) {
  return (type.kind == "matrix" || type.kind == "sequence" ||
          type.kind == "variant" || type.kind == "vector" ||
          type.kind == "groups" || type.kind == "indices" ||
          type.kind == "bytes") &&
         nativeMessageData(type);
}
bool nativeSetupType(const BoundType &type);
// String overloads are boundary readers. All recursive policy uses borrowed
// structured types, including every inactive variant alternative.
bool duplicable(const BoundType &type);
bool discardable(const BoundType &type);
bool duplicable(llvm::StringRef type);
bool discardable(llvm::StringRef type);
Custody custody(llvm::StringRef type);
inline bool hasTypeProperties(llvm::StringRef type) {
  return custody(type) != Custody::Unknown;
}
inline bool affine(llvm::StringRef type) {
  return custody(type) == Custody::Affine;
}
// This describes a codec, not information-flow authorization to send a secret.
inline bool serializable(llvm::StringRef type) {
  return custody(type) == Custody::PublicValue;
}
} // namespace zkc::protocol
#endif
