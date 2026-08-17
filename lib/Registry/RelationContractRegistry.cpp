//===- RelationContractRegistry.cpp - Relation contracts -------*- C++ -*-===//
// Loader-time admission of the relation-contract vocabulary
// (docs/spec/relations.md). A contract states how one relation's
// interface is read and how its public instance corresponds to a
// sealed protocol's statement; the reading is post-seal evidence, so
// admission's whole job is that every declared fact is well shaped and
// that nothing here can be mistaken for a fact zkc verified.
//
// Two admission rules carry more than shape. The anchor partition is
// held to the normative table below rather than to whatever a contract
// declares, because which anchors of a profile identify the relation
// is a fact about the profile; letting each contract re-declare it
// would let one contract silently cover different relations. And the
// instance encoding has no default: the surveyed relation families do
// not share one, so an omitted encoding refuses rather than picking a
// family's shape for it.
//===----------------------------------------------------------------------===//

#include "zkc/Registry/RelationContractRegistry.h"

#include "zkc/Encoding/EncodingDomain.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>

using namespace llvm;
using namespace zkc::registry;

//===----------------------------------------------------------------------===//
// The normative anchor partition (docs/spec/relations.md §2.3)
//===----------------------------------------------------------------------===//

namespace {
constexpr StringRef kR1csRelation[] = {"a", "b", "c"};
constexpr StringRef kR1csInstance[] = {"public"};
constexpr StringRef kOpaqueRelation[] = {"contract"};
constexpr StringRef kOpaqueInstance[] = {"statement"};

struct PartitionRow {
  StringRef profile;
  AnchorPartition partition;
};

const PartitionRow kPartitions[] = {
    {"r1cs", {kR1csRelation, kR1csInstance}},
    {"opaque_relation", {kOpaqueRelation, kOpaqueInstance}},
};
} // namespace

const AnchorPartition *
zkc::registry::normativeAnchorPartition(StringRef profileName) {
  for (const PartitionRow &row : kPartitions)
    if (row.profile == profileName)
      return &row.partition;
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Canonical form
//===----------------------------------------------------------------------===//

json::Value InstanceEncoding::toCanonicalJson() const {
  switch (kind) {
  case InstanceEncodingKind::FieldVector:
    return json::Object{
        {"arity", arity}, {"field_order", fieldOrder}, {"kind", "field_vector"}};
  case InstanceEncodingKind::OpaqueBytes:
    return json::Object{{"digest_function", digestFunction},
                        {"kind", "opaque_bytes"}};
  case InstanceEncodingKind::Commitment:
    return json::Object{{"kind", "commitment"}, {"payload_class", payloadClass}};
  }
  llvm_unreachable("closed instance-encoding kind");
}

json::Value WitnessPorts::toCanonicalJson() const {
  if (opaque)
    return json::Object{
        {"kind", "opaque"},
        {"port", json::Object{{"name", ports.front().name}}}};
  json::Array entries;
  for (const WitnessPort &port : ports)
    entries.push_back(json::Object{{"count", port.count}, {"name", port.name}});
  return json::Object{{"kind", "enumerated"}, {"ports", std::move(entries)}};
}

json::Value RelationContract::toCanonicalJson() const {
  json::Object anchors;
  for (const auto &[name, value] : relationAnchors)
    anchors[name] = value;
  json::Array instances;
  for (const std::string &name : instanceAnchors)
    instances.push_back(name);
  json::Object identity;
  if (!contentDigest.empty())
    identity["content_digest"] = contentDigest;
  if (!attestedId.empty()) {
    identity["attested_id"] = attestedId;
    identity["attestor"] = attestor;
  }
  json::Array wiring;
  for (const CorrespondenceEntry &entry : correspondence)
    wiring.push_back(json::Object{{"label", entry.label}, {"slot", entry.slot}});

  json::Object body{
      {"claim_profile",
       json::Object{{"digest", profileDigest}, {"name", profileName}}},
      {"format", format},
      {"identity", std::move(identity)},
      {"instance_anchors", std::move(instances)},
      {"instance_encoding", instanceEncoding.toCanonicalJson()},
      {"relation_anchors", std::move(anchors)},
      {"statement_correspondence", std::move(wiring)},
      {"witness_ports", witnessPorts.toCanonicalJson()}};
  if (constraintCount)
    body["declared_shape"] = json::Object{{"constraint_count", *constraintCount}};
  return json::Value(std::move(body));
}

//===----------------------------------------------------------------------===//
// Admission
//===----------------------------------------------------------------------===//

Expected<RelationContract>
RelationContractRegistry::parseEntry(const RegistryFile &file, StringRef name,
                                     const json::Value &value) {
  std::string context = ("relation contract '" + name + "'").str();
  auto err = [&](const Twine &message) {
    return file.error(context + ": " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return err("must map to an object");
  if (Error e = file.requireClosedFields(
          *object,
          {"claim_profile", "relation_anchors", "instance_anchors", "format",
           "identity", "instance_encoding", "witness_ports",
           "statement_correspondence", "declared_shape"},
          context))
    return std::move(e);

  RelationContract contract;

  // -- The profile, pinned by name and content digest so a vocabulary
  // -- edit cannot change what a fixed contract means.
  const json::Object *profile = object->getObject("claim_profile");
  if (!profile)
    return err("'claim_profile' must be an object {name, digest}");
  if (Error e = file.requireClosedFields(*profile, {"name", "digest"},
                                         context + " claim_profile"))
    return std::move(e);
  if (Error e = file.requireStringField(*profile, "name",
                                        context + " claim_profile",
                                        contract.profileName))
    return std::move(e);
  if (Error e = file.requireStringField(*profile, "digest",
                                        context + " claim_profile",
                                        contract.profileDigest))
    return std::move(e);
  if (!zkc::encoding::isSha256Ref(contract.profileDigest))
    return err("'claim_profile.digest' must be sha256:<64 lowercase hex>");

  // -- The partition, held to the normative table rather than to the
  // -- contract's own say-so.
  const AnchorPartition *partition =
      normativeAnchorPartition(contract.profileName);
  if (!partition)
    return err("claim profile '" + contract.profileName +
               "' has no admitted anchor partition");

  const json::Object *relationAnchors = object->getObject("relation_anchors");
  if (!relationAnchors)
    return err("'relation_anchors' must be an object from anchor name to "
               "sha256 value");
  for (const auto &anchor : *relationAnchors) {
    StringRef anchorName(anchor.first);
    std::optional<StringRef> anchorValue = anchor.second.getAsString();
    if (!anchorValue || !zkc::encoding::isSha256Ref(*anchorValue))
      return err("relation anchor '" + anchorName +
                 "' must be sha256:<64 lowercase hex>");
    if (!is_contained(partition->relationAnchors, anchorName))
      return err("relation anchor '" + anchorName +
                 "' is not a relation-level anchor of profile '" +
                 contract.profileName + "'");
    contract.relationAnchors[anchorName.str()] = anchorValue->str();
  }
  if (contract.relationAnchors.size() != partition->relationAnchors.size())
    return err("'relation_anchors' must carry exactly the profile's "
               "relation-level anchors");

  auto instanceAnchors =
      file.requireStringList(*object, "instance_anchors", context);
  if (!instanceAnchors)
    return instanceAnchors.takeError();
  contract.instanceAnchors = std::move(*instanceAnchors);
  if (contract.instanceAnchors.size() != partition->instanceAnchors.size())
    return err("'instance_anchors' must carry exactly the profile's "
               "instance-level anchors");
  for (auto it = contract.instanceAnchors.begin();
       it != contract.instanceAnchors.end(); ++it) {
    if (!is_contained(partition->instanceAnchors, *it))
      return err("instance anchor '" + *it +
                 "' is not an instance-level anchor of profile '" +
                 contract.profileName + "'");
    // Size-plus-membership admits a repeat once a profile has two
    // instance anchors, which would leave the other unmentioned.
    if (std::find(contract.instanceAnchors.begin(), it, *it) != it)
      return err("instance anchor '" + *it + "' is named twice");
  }

  // -- The reading form: closed, and a name without stated reading
  // -- rules is not admitted.
  if (Error e =
          file.requireStringField(*object, "format", context, contract.format))
    return std::move(e);
  if (contract.format != "r1cs-bin-v1" && contract.format != "opaque")
    return err("unknown format '" + contract.format +
               "' (the admitted set is r1cs-bin-v1, opaque)");

  // -- Identity: two primitives, never merged, at least one present.
  const json::Object *identity = object->getObject("identity");
  if (!identity)
    return err("'identity' must be an object");
  if (Error e = file.requireClosedFields(
          *identity, {"content_digest", "attested_id", "attestor"},
          context + " identity"))
    return std::move(e);
  if (identity->get("content_digest")) {
    if (Error e = file.requireStringField(*identity, "content_digest",
                                          context + " identity",
                                          contract.contentDigest))
      return std::move(e);
    if (!zkc::encoding::isSha256Ref(contract.contentDigest))
      return err("'identity.content_digest' must be sha256:<64 lowercase hex>");
  }
  if (identity->get("attested_id")) {
    if (Error e = file.requireStringField(*identity, "attested_id",
                                          context + " identity",
                                          contract.attestedId))
      return std::move(e);
    // An attested id is an external party's assertion; without the
    // party the assertion has no subject, so the ledger could not name
    // whose word a judgment rests on.
    if (Error e = file.requireStringField(
            *identity, "attestor", context + " identity", contract.attestor))
      return std::move(e);
  } else if (identity->get("attestor")) {
    return err("'identity.attestor' names the party asserting an "
               "'attested_id'; there is none");
  }
  if (contract.contentDigest.empty() && contract.attestedId.empty())
    return err("'identity' needs at least one of 'content_digest' (zkc "
               "computed it) and 'attested_id' (a named party asserts it)");

  // -- The public-instance encoding: no default (docs/spec/relations.md
  // -- §2.4). The families do not share one.
  const json::Object *encoding = object->getObject("instance_encoding");
  if (!encoding)
    return err("'instance_encoding' must be an object; there is no default");
  auto encodingKind = file.requireString(*encoding, "kind",
                                         context + " instance_encoding");
  if (!encodingKind)
    return encodingKind.takeError();
  if (*encodingKind == "field_vector") {
    contract.instanceEncoding.kind = InstanceEncodingKind::FieldVector;
    if (Error e = file.requireClosedFields(*encoding,
                                           {"kind", "field_order", "arity"},
                                           context + " instance_encoding"))
      return std::move(e);
    if (Error e = file.requireStringField(*encoding, "field_order",
                                          context + " instance_encoding",
                                          contract.instanceEncoding.fieldOrder))
      return std::move(e);
    for (char c : contract.instanceEncoding.fieldOrder)
      if (!isDigit(c))
        return err("'instance_encoding.field_order' must be a decimal integer "
                   "string");
    if (contract.instanceEncoding.fieldOrder.front() == '0')
      return err("'instance_encoding.field_order' must have no leading zeros");
    std::optional<int64_t> arity = encoding->getInteger("arity");
    if (!arity || *arity < 0)
      return err("'instance_encoding.arity' must be a non-negative integer");
    contract.instanceEncoding.arity = *arity;
  } else if (*encodingKind == "opaque_bytes") {
    contract.instanceEncoding.kind = InstanceEncodingKind::OpaqueBytes;
    if (Error e = file.requireClosedFields(*encoding, {"kind", "digest_function"},
                                           context + " instance_encoding"))
      return std::move(e);
    if (Error e = file.requireStringField(
            *encoding, "digest_function", context + " instance_encoding",
            contract.instanceEncoding.digestFunction))
      return std::move(e);
    // The hash a consumer applies is part of the interface: two
    // consumers assuming different functions over one byte stream
    // disagree about which instance was proven.
    if (contract.instanceEncoding.digestFunction != "sha256")
      return err("unknown 'instance_encoding.digest_function' '" +
                 contract.instanceEncoding.digestFunction +
                 "' (the admitted set is sha256)");
  } else if (*encodingKind == "commitment") {
    contract.instanceEncoding.kind = InstanceEncodingKind::Commitment;
    if (Error e = file.requireClosedFields(*encoding, {"kind", "payload_class"},
                                           context + " instance_encoding"))
      return std::move(e);
    if (Error e = file.requireStringField(
            *encoding, "payload_class", context + " instance_encoding",
            contract.instanceEncoding.payloadClass))
      return std::move(e);
  } else {
    return err("unknown 'instance_encoding.kind' '" + *encodingKind +
               "' (the admitted set is field_vector, opaque_bytes, "
               "commitment)");
  }

  // -- Witness ports: enumerated or opaque, because the families
  // -- genuinely differ and forcing one shape misdescribes the other.
  const json::Object *ports = object->getObject("witness_ports");
  if (!ports)
    return err("'witness_ports' must be an object");
  auto portsKind = file.requireString(*ports, "kind", context + " witness_ports");
  if (!portsKind)
    return portsKind.takeError();
  if (*portsKind == "enumerated") {
    if (Error e = file.requireClosedFields(*ports, {"kind", "ports"},
                                           context + " witness_ports"))
      return std::move(e);
    const json::Array *list = ports->getArray("ports");
    if (!list || list->empty())
      return err("'witness_ports.ports' must be a non-empty array");
    for (const json::Value &entry : *list) {
      const json::Object *port = entry.getAsObject();
      if (!port)
        return err("each witness port must be an object {name, count}");
      if (Error e = file.requireClosedFields(*port, {"name", "count"},
                                             context + " witness port"))
        return std::move(e);
      WitnessPort parsed;
      if (Error e = file.requireStringField(*port, "name",
                                            context + " witness port",
                                            parsed.name))
        return std::move(e);
      std::optional<int64_t> count = port->getInteger("count");
      if (!count || *count < 0)
        return err("witness port '" + parsed.name +
                   "' needs a non-negative integer 'count'");
      parsed.count = *count;
      for (const WitnessPort &seen : contract.witnessPorts.ports)
        if (seen.name == parsed.name)
          return err("witness port '" + parsed.name + "' is declared twice");
      contract.witnessPorts.ports.push_back(std::move(parsed));
    }
  } else if (*portsKind == "opaque") {
    contract.witnessPorts.opaque = true;
    if (Error e = file.requireClosedFields(*ports, {"kind", "port"},
                                           context + " witness_ports"))
      return std::move(e);
    const json::Object *port = ports->getObject("port");
    if (!port)
      return err("'witness_ports.port' must be an object {name}");
    if (Error e = file.requireClosedFields(*port, {"name"},
                                           context + " witness port"))
      return std::move(e);
    WitnessPort parsed;
    if (Error e = file.requireStringField(*port, "name",
                                          context + " witness port", parsed.name))
      return std::move(e);
    contract.witnessPorts.ports.push_back(std::move(parsed));
  } else {
    return err("unknown 'witness_ports.kind' '" + *portsKind +
               "' (the admitted set is enumerated, opaque)");
  }

  // -- The correspondence: the permutation between instance positions
  // -- and statement labels. Slots are the instance order, exactly
  // -- once each; labels are checked against an artifact's ABI by the
  // -- correspondence judgment, not here.
  const json::Array *wiring = object->getArray("statement_correspondence");
  if (!wiring)
    return err("'statement_correspondence' must be an array");
  for (const json::Value &entry : *wiring) {
    const json::Object *pair = entry.getAsObject();
    if (!pair)
      return err("each correspondence entry must be an object {slot, label}");
    if (Error e = file.requireClosedFields(*pair, {"slot", "label"},
                                           context + " correspondence"))
      return std::move(e);
    CorrespondenceEntry parsed;
    std::optional<int64_t> slot = pair->getInteger("slot");
    if (!slot || *slot < 0)
      return err("correspondence 'slot' must be a non-negative integer");
    parsed.slot = *slot;
    if (Error e = file.requireStringField(*pair, "label",
                                          context + " correspondence",
                                          parsed.label))
      return std::move(e);
    for (const CorrespondenceEntry &seen : contract.correspondence) {
      if (seen.slot == parsed.slot)
        return err("correspondence slot " + Twine(parsed.slot) +
                   " is wired twice");
      if (seen.label == parsed.label)
        return err("correspondence label '" + parsed.label +
                   "' is wired twice");
    }
    contract.correspondence.push_back(std::move(parsed));
  }
  // The instance positions a correspondence covers are a prefix-free
  // set of the instance order; a gap would leave a slot's wiring
  // unstated while the count still looked complete.
  for (size_t index = 0; index < contract.correspondence.size(); ++index) {
    bool found = false;
    for (const CorrespondenceEntry &entry : contract.correspondence)
      found |= entry.slot == static_cast<int64_t>(index);
    if (!found)
      return err("correspondence slots must be 0..n-1 without gaps");
  }
  if (contract.instanceEncoding.kind == InstanceEncodingKind::FieldVector &&
      contract.correspondence.size() !=
          static_cast<size_t>(contract.instanceEncoding.arity))
    return err("'statement_correspondence' must cover every instance "
               "position: the declared arity is " +
               Twine(contract.instanceEncoding.arity) + ", the wiring covers " +
               Twine(contract.correspondence.size()));

  // -- Optional shape facts a soundness rule reads.
  if (const json::Object *shape = object->getObject("declared_shape")) {
    if (Error e = file.requireClosedFields(*shape, {"constraint_count"},
                                           context + " declared_shape"))
      return std::move(e);
    std::optional<int64_t> count = shape->getInteger("constraint_count");
    if (!count || *count < 0)
      return err("'declared_shape.constraint_count' must be a non-negative "
                 "integer");
    contract.constraintCount = *count;
  } else if (object->get("declared_shape")) {
    return err("'declared_shape' must be an object");
  }

  // A reading form and an instance encoding are not independent: the
  // r1cs header states a field and a public arity, so an r1cs contract
  // whose instance is not a field vector would leave the reader without
  // the declared width that bounds it.
  if (contract.format == "r1cs-bin-v1" &&
      contract.instanceEncoding.kind != InstanceEncodingKind::FieldVector)
    return err("format 'r1cs-bin-v1' reads a field-vector instance; this "
               "contract declares another encoding");

  auto digest = RegistryFile::digestEntry("zkc/relation-contract\n",
                                          contract.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  contract.digest = std::move(*digest);
  return contract;
}
