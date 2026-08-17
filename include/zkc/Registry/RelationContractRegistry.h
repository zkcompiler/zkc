//===- RelationContractRegistry.h - Relation contracts ----------*- C++ -*-===//
#ifndef ZKC_REGISTRY_RELATIONCONTRACTREGISTRY_H
#define ZKC_REGISTRY_RELATIONCONTRACTREGISTRY_H

#include "zkc/Registry/RegistryBase.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace zkc {
namespace registry {

/// How a relation's public instance is represented
/// (docs/spec/relations.md §2.4). Three admitted forms, no default:
/// the surveyed relation families do not share one, and picking a
/// default would misdescribe whichever family did not get it.
enum class InstanceEncodingKind {
  FieldVector, // ordered field elements: the constraint family
  OpaqueBytes, // a byte stream the consumer identifies by digest
  Commitment,  // the instance is itself a commitment value
};

struct InstanceEncoding {
  InstanceEncodingKind kind = InstanceEncodingKind::FieldVector;
  std::string fieldOrder;     // FieldVector: exact cardinality, decimal
  int64_t arity = 0;          // FieldVector: element count
  std::string digestFunction; // OpaqueBytes: the consumer's exact hash
  std::string payloadClass;   // Commitment: the sealed payload class

  llvm::json::Value toCanonicalJson() const;
};

/// A relation's private-input interface (docs/spec/relations.md §2.5).
/// Enumerated ports for relations whose witness is a declared variable
/// range; one opaque port where the witness is a whole object and no
/// port list exists to declare.
struct WitnessPort {
  std::string name;
  int64_t count = 0; // enumerated only
};

struct WitnessPorts {
  bool opaque = false;
  std::vector<WitnessPort> ports; // enumerated: many; opaque: exactly one

  llvm::json::Value toCanonicalJson() const;
};

/// One entry of the ordered wiring between a relation's public-instance
/// positions and a sealed protocol's statement labels
/// (docs/spec/relations.md §2.6). The list is the permutation: it need
/// not preserve the artifact's ABI order, because instance order and
/// absorption order are independent.
struct CorrespondenceEntry {
  int64_t slot = 0;
  std::string label;
};

/// The interface of one relation and its correspondence to sealed
/// protocols that cite that relation through claim anchors
/// (docs/spec/relations.md). Evidence-only for every artifact it
/// describes; its own digest is identity-bearing exactly where another
/// identity-bearing object pins it.
struct RelationContract {
  // The profile whose anchors this contract partitions, pinned by name
  // and content digest so a vocabulary edit cannot change what a fixed
  // contract means.
  std::string profileName;
  std::string profileDigest;

  // The partition (§2.3). Relation anchors carry the values the
  // contract is scoped to; instance anchors are names only, checked
  // per artifact.
  std::map<std::string, std::string, std::less<>> relationAnchors;
  std::vector<std::string> instanceAnchors;

  // The closed reading form for relation-artifact bytes (§2.2).
  std::string format;

  // Identity (§2.1): two primitives that never merge. At least one is
  // present; an attested id carries its attestor.
  std::string contentDigest;
  std::string attestedId;
  std::string attestor;

  InstanceEncoding instanceEncoding;
  WitnessPorts witnessPorts;
  std::vector<CorrespondenceEntry> correspondence;

  // Optional relation-shape facts a soundness rule reads (§2.7); each
  // lands as the existing assumption pattern until bytes make it
  // checkable.
  std::optional<int64_t> constraintCount;

  /// The entry's tagged content digest, computed at load.
  std::string digest;

  llvm::json::Value toCanonicalJson() const;

  bool attestedOnly() const { return contentDigest.empty(); }
};

/// The relation-contract registry (docs/spec/relations.md §1):
///
/// ```json
/// {
///   "registry": "zkc.relation_contract",
///   "contracts": {
///     "toy.r1cs.entry": {
///       "claim_profile": {"name": "r1cs", "digest": "sha256:..."},
///       "relation_anchors": {"a": "sha256:...", "b": "sha256:...",
///                            "c": "sha256:..."},
///       "instance_anchors": ["public"],
///       "format": "r1cs-bin-v1",
///       "identity": {"attested_id": "...", "attestor": "..."},
///       "instance_encoding": {"kind": "field_vector",
///                             "field_order": "...", "arity": 2},
///       "witness_ports": {"kind": "enumerated",
///                         "ports": [{"name": "assignment", "count": 5}]},
///       "statement_correspondence": [{"slot": 0, "label": "x"}]
///     }
///   }
/// }
/// ```
///
/// The registry map key is a lookup handle and is not covered by the
/// entry digest; no judgment resolves a contract by name.
class RelationContractRegistry
    : public RegistryBase<RelationContractRegistry, RelationContract> {
  friend class RegistryBase<RelationContractRegistry, RelationContract>;

  static constexpr llvm::StringLiteral kRegistryName = "zkc.relation_contract";
  static constexpr llvm::StringLiteral kPayloadField = "contracts";
  static constexpr llvm::StringLiteral kEntryNoun = "relation contract";

  static llvm::Expected<RelationContract>
  parseEntry(const RegistryFile &file, llvm::StringRef name,
             const llvm::json::Value &value);
};

/// The normative anchor partition per admitted claim profile
/// (docs/spec/relations.md §2.3): which of a profile's anchors identify
/// the relation and which identify one instance. Stated once, here,
/// because it is a fact about the profile rather than about any one
/// contract — a contract that disagrees refuses at admission.
/// Returns null for a profile with no admitted partition.
struct AnchorPartition {
  llvm::ArrayRef<llvm::StringRef> relationAnchors;
  llvm::ArrayRef<llvm::StringRef> instanceAnchors;
};
const AnchorPartition *normativeAnchorPartition(llvm::StringRef profileName);

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_RELATIONCONTRACTREGISTRY_H
