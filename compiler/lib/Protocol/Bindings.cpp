#include "zkc/Protocol/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Domains.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Protocol/Module.h"
#include "zkc/Protocol/ResourceUnit.h"
#include "zkc/Protocol/Variant.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <map>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
bool name(StringRef value) {
  return !value.empty() && value.size() <= 256 &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-' || c == '/';
         });
}

} // namespace

StringRef defaultCodec(const BoundType &logical) {
  if (!logical.representation.empty())
    return {};
  const auto *codec =
      installedDomains().defaultCodec(logical.kind, logical.identity);
  return codec ? StringRef(codec->identity) : StringRef{};
}

bool BoundType::operator==(const BoundType &other) const {
  return kind == other.kind && identity == other.identity &&
         representation == other.representation;
}

StringRef installedIdentitySort(StringRef identity) {
  return installedDomains().identitySort(identity);
}
StringRef associatedIdentity(StringRef identity, StringRef key) {
  return installedDomains().associatedIdentity(identity, key);
}

namespace {
// Representation applicability and implementation availability are independent.
// Transcript implementation selection is nominal and independent of payload
// providers.
StringRef backendFor(StringRef identity) {
  StringRef sort = installedDomains().identitySort(identity);
  if (sort == "Transcript") {
    if (identity == "spongefish0.7.4.keccak.bls12-381.fr64be/1")
      return "spongefish";
    identity = associatedIdentity(identity, "ChallengeField");
  } else if (sort == "Commitment")
    identity = associatedIdentity(identity, "ValueField");
  const auto *rep = installedDomains().defaultRepresentation(
      sort == "Group" ? "group" : "field", identity);
  if (!rep)
    return {};
  if (StringRef(rep->identity).starts_with("arkworks."))
    return "arkworks";
  if (StringRef(rep->identity).starts_with("dalek."))
    return "dalek";
  if (StringRef(rep->identity).starts_with("plonky3."))
    return "plonky3";
  return {};
}
} // namespace

bool isDiagonalRepresentation(StringRef representation) {
  return representation == "arkworks.fr-diagonal/1" ||
         representation == "dalek.ristretto-diagonal/1";
}

Expected<std::string>
defaultImplementation(const source::OperationBinding &binding) {
  // Resolve logical formation first. This does not invent support for an
  // installed field whose required carriers have no implementation.
  auto logical = resolveBinding(binding, false);
  if (!logical)
    return logical.takeError();
  if (resourceUnitContract(binding.contract))
    return "logical/" + binding.contract;
  StringRef backend;
  if (StringRef(binding.contract).starts_with("index.") ||
      StringRef(binding.contract).starts_with("indices.") ||
      StringRef(binding.contract).starts_with("external."))
    return "native/" + binding.contract;
  // A transcript implementation consumes codecs from its associated field;
  // those codecs need not be implemented by the transcript provider.
  const bool transcript =
      StringRef(binding.contract).starts_with("transcript.");
  for (const auto &argument : binding.arguments) {
    if (transcript && !backend.empty())
      break;
    if (installedIdentitySort(argument) == "Codec")
      continue;
    auto candidate = backendFor(argument);
    if (candidate.empty() || (!backend.empty() && candidate != backend))
      return error("binding-implementation");
    backend = candidate;
  }
  std::string result = ((backend.empty() ? StringRef("arkworks") : backend) +
                        "/" + binding.contract)
                           .str();
  auto selected = binding;
  selected.implementation = result;
  auto physical = resolveBinding(selected, true);
  if (!physical)
    return physical.takeError();
  return result;
}

Error checkImplementation(StringRef contract, StringRef implementation) {
  if (resourceUnitContract(contract))
    return implementation == ("logical/" + contract).str()
               ? Error::success()
               : error("binding-implementation");
  if (none_of(boundOperationContracts(),
              [&](const auto &op) { return op.name == contract; }))
    return error("binding-contract");
  if (contract.starts_with("index.") || contract.starts_with("indices.") ||
      contract.starts_with("external."))
    return implementation == ("native/" + contract).str()
               ? Error::success()
               : error("binding-implementation");
  if ((contract.starts_with("transcript.") &&
       implementation == ("spongefish/" + contract).str()) ||
      implementation == ("arkworks/" + contract).str() ||
      implementation == ("dalek/" + contract).str() ||
      implementation == ("plonky3/" + contract).str() ||
      ((contract == "poly.product_sum" || contract == "poly.product_round" ||
        contract == "poly.boundary" || contract == "poly.round_evaluate" ||
        contract == "poly.fold" || contract == "poly.evaluate" ||
        contract == "poly.empty_point" || contract == "poly.append_point" ||
        contract == "vector.from_table" || contract == "vector.to_table") &&
       implementation == ("arkworks-msb/" + contract).str()) ||
      ((contract == "vector.mul" || contract == "vector.dot") &&
       implementation == ("arkworks-diagonal/" + contract).str()) ||
      ((contract == "curve.scale_each" || contract == "curve.msm") &&
       implementation == ("dalek-diagonal/" + contract).str()) ||
      (contract == "curve.msm" && implementation == "dalek-vartime/curve.msm"))
    return Error::success();
  return error("binding-implementation");
}

Error checkStaticVocabulary(const generic::Signature &signature) {
  for (const auto &sort : signature.scope.sorts)
    if (sort != "Field" && sort != "Group" && sort != "Commitment" &&
        sort != "Transcript" && sort != "Codec")
      return error("generic-declared-sort");
  for (const auto &predicate : signature.requirements) {
    if (predicate.kind == requirements::Predicate::Kind::Equal)
      continue; // Equality formation, including sort agreement, is generic.
    StringRef key = predicate.relation;
    std::vector<StringRef> sorts;
    if (key == "Field" || key == "CommRing" || key == "PrimeField" ||
        key == "ExtensionField" || key == "TwoAdicField" ||
        key == "CharacteristicNotTwo" || key == "IndexRandomness" ||
        key == "PairingField")
      sorts = {"Field"};
    else if (key == "Group" || key == "ScalarAction")
      sorts = {"Group"};
    else if (key == "MultilinearOpening" || key == "VectorCommitment")
      sorts = {"Commitment"};
    else if (key == "Transcript" || key == "FieldTranscript" ||
             key == "IndexTranscript")
      sorts = {"Transcript"};
    else if (key.consume_front("Encodes.")) {
      const generic::TypeConstructor *type = nullptr;
      for (const auto &candidate : boundTypeConstructors())
        if (candidate.name == key &&
            (key == "bool" || key == "index" || key == "indices" ||
             key == "field" || key == "table" || key == "point" ||
             key == "round" || key == "group" || key == "matrix" ||
             key == "groups" || key == "vector" || key == "polynomial" ||
             key == "commitment" || key == "commitments" || key == "proof"))
          type = &candidate;
      if (!type)
        return error("generic-declared-predicate");
      sorts.push_back("Codec");
      for (const auto &sort : type->parameters)
        sorts.push_back(sort);
    } else
      return error("generic-declared-predicate");
    if (sorts.size() != predicate.arguments.size())
      return error("generic-predicate-arity");
    for (auto [index, sort] : zip(predicate.arguments, sorts))
      if (index >= signature.scope.sorts.size() ||
          signature.scope.sorts[index] != sort)
        return error("generic-predicate-sort");
  }
  return Error::success();
}

StringRef associatedMemberSort(StringRef sort, StringRef name) {
  if (sort == "Field" && (name == "PairingG1" || name == "PairingG2"))
    return "Group";
  if ((sort == "Field" && name == "BaseField") ||
      (sort == "Group" && name == "Scalar") ||
      (sort == "Commitment" && (name == "ValueField" || name == "PointField" ||
                                name == "EvaluationField")) ||
      (sort == "Transcript" && name == "ChallengeField"))
    return "Field";
  return {};
}

Expected<std::vector<std::string>>
resolveStaticArguments(const generic::Scope &scope,
                       ArrayRef<std::string> arguments) {
  if (scope.terms.size() != scope.sorts.size() || scope.terms.size() > 128)
    return error("binding-static-scope");
  std::vector<std::string> selected;
  size_t next = 0;
  for (auto [i, term] : enumerate(scope.terms)) {
    if (term.arguments)
      return error("binding-static-application");
    StringRef identity;
    if (term.parent) {
      if (*term.parent >= i)
        return error("binding-static-scope");
      identity = installedDomains().associatedIdentity(selected[*term.parent],
                                                       term.name);
    } else if (auto fixed = scope.constants.find(i);
               fixed != scope.constants.end()) {
      identity = fixed->second;
    } else {
      if (next >= arguments.size())
        return error("binding-static-arity");
      identity = arguments[next++];
    }
    if (identity.empty() ||
        installedDomains().identitySort(identity) != scope.sorts[i])
      return error("binding-static-identity");
    selected.push_back(identity.str());
  }
  if (next != arguments.size())
    return error("binding-static-arity");
  return selected;
}

Error checkClosedRequirements(ArrayRef<requirements::Predicate> predicates,
                              ArrayRef<std::string> selected) {
  for (const auto &p : predicates) {
    std::vector<std::string> arguments;
    for (unsigned i : p.arguments) {
      if (i >= selected.size())
        return error("binding-static-scope");
      arguments.push_back(selected[i]);
    }
    if (p.kind == requirements::Predicate::Kind::Equal
            ? arguments.size() != 2 || arguments[0] != arguments[1]
            : !installedDomains().hasFact(p.relation, arguments))
      return error("binding-requirement");
  }
  return Error::success();
}

std::string BoundType::spelling() const {
  return kind + (identity.empty() ? "" : ":" + identity) +
         (representation.empty() ? "" : "@" + representation);
}

ArrayRef<generic::TypeConstructor> boundTypeConstructors() {
  static const std::vector<generic::TypeConstructor> types = {
      {"bool", {}},
      {"index", {}},
      {"indices", {}},
      {"field", {"Field"}},
      {"vector", {"Field"}},
      {"matrix", {"Field"}},
      {"polynomial", {"Field"}},
      {"table", {"Field"}},
      {"point", {"Field"}},
      {"round", {"Field"}},
      {"rng", {"Field"}, true},
      {"nonce", {"Field"}, true},
      {"group", {"Group"}},
      {"groups", {"Group"}},
      {"transcript", {"Transcript"}, true},
      {"commitment", {"Commitment"}},
      {"commitments", {"Commitment"}},
      {"opening_states", {"Commitment"}},
      {"proof", {"Commitment"}},
      {"prover_key", {"Commitment"}},
      {"verifier_key", {"Commitment"}},
      {"opening_state", {"Commitment"}}};
  return types;
}

Expected<BoundType> parseBoundType(StringRef spelling, bool physical) {
  if (spelling.size() > (spelling.starts_with("variant:")
                             ? VariantSpellingBytes + (physical ? 18 : 0)
                             : 4096))
    return error("binding-type-limit");
  auto [logical, rep] = spelling.split('@');
  auto [kind, identity] = logical.split(':');
  if (physical != spelling.contains('@') || (physical && !name(rep)))
    return error("binding-representation");
  if (kind == "variant") {
    auto descriptor = decodeVariant(logical.str());
    if (!descriptor)
      return error("variant-type");
    if (physical && rep != "logical.variant/1")
      return error("binding-representation");
    if (physical)
      for (const auto &arm : descriptor->alternatives)
        for (const auto &leaf : arm.payload) {
          auto parsed = parseBoundType(leaf, false);
          if (!parsed)
            return parsed.takeError();
          auto selected = defaultRepresentation(*parsed);
          if (!selected)
            return selected.takeError();
        }
    return BoundType{kind.str(), identity.str(), rep.str()};
  }
  if (kind == "resource_unit") {
    if (!resourceUnitDomain(identity))
      return error("binding-type-identity");
    if (physical && rep != "logical.resource_unit/1")
      return error("binding-representation");
    return BoundType{kind.str(), identity.str(), rep.str()};
  }
  for (const auto &t : boundTypeConstructors()) {
    if (t.name != kind)
      continue;
    if (t.parameters.empty()
            ? !identity.empty() || logical.contains(':')
            : installedDomains().identitySort(identity) != t.parameters[0])
      return error("binding-type-identity");
    // Sort agreement alone admits pairs such as a table over a field no
    // backend tabulates. The logical pair is one the installed catalog
    // carries, the same exact kind/identity set the independent readers admit.
    if (!t.parameters.empty() &&
        !installedDomains().defaultRepresentation(kind, identity))
      return error("binding-type-identity");
    if (physical && !installedDomains().representation(kind, identity, rep))
      return error("binding-representation");
    return BoundType{kind.str(), identity.str(), rep.str()};
  }
  return error("binding-type");
}

Expected<BoundType> defaultRepresentation(const BoundType &logical) {
  if (!logical.representation.empty())
    return error("binding-physical-type-at-logical-stage");
  // Validate the logical type first, preserving its existing refusal codes.
  auto checked = parseBoundType(logical.spelling(), false);
  if (!checked)
    return checked.takeError();
  if (logical.kind == "variant")
    return parseBoundType(logical.spelling() + "@logical.variant/1", true);
  if (logical.kind == "resource_unit")
    return BoundType{logical.kind, logical.identity, "logical.resource_unit/1"};
  const auto *rep =
      installedDomains().defaultRepresentation(logical.kind, logical.identity);
  if (!rep)
    return error("binding-representation");
  auto result = logical;
  result.representation = rep->identity;
  return parseBoundType(result.spelling(), true);
}

Type decodeBoundType(MLIRContext *ctx, const BoundType &t) {
  Type result;
  if (t.kind == "variant")
    result = VariantType::get(ctx, "variant:" + t.identity);
  else if (t.kind == "bool")
    result = IntegerType::get(ctx, 1);
  else if (t.kind == "index")
    result = IntegerType::get(ctx, 64, IntegerType::Unsigned);
  else if (t.kind == "indices")
    result =
        RankedTensorType::get({ShapedType::kDynamic},
                              IntegerType::get(ctx, 64, IntegerType::Unsigned));
  else if (t.kind == "field")
    result = FieldType::get(ctx, t.identity);
  else if (t.kind == "matrix")
    result = MatrixType::get(ctx, t.identity);
  else if (t.kind == "table")
    result = MultilinearType::get(ctx, t.identity);
  else if (t.kind == "point")
    result = PointType::get(ctx, t.identity);
  else if (t.kind == "round")
    result = QuadraticType::get(ctx, t.identity);
  else if (t.kind == "group")
    result = GroupType::get(ctx, t.identity);
  else if (t.kind == "vector" || t.kind == "groups")
    result = RankedTensorType::get({ShapedType::kDynamic},
                                   t.kind == "vector"
                                       ? Type(FieldType::get(ctx, t.identity))
                                       : Type(GroupType::get(ctx, t.identity)));
  else if (t.kind == "polynomial")
    result = UnivariateType::get(ctx, t.identity);
  else if (t.kind == "resource_unit" || t.kind == "rng" || t.kind == "nonce" ||
           t.kind == "transcript")
    result = CapabilityType::get(ctx, t.kind + ":" + t.identity);
  else if (installedDomains().hasFact("VectorCommitment", {t.identity}))
    result = OracleObjectType::get(ctx, t.identity, t.kind);
  else
    result = ObjectType::get(ctx, t.identity, t.kind);
  return t.representation.empty()
             ? result
             : DataType::get(ctx, result, t.representation);
}

Expected<BoundType> encodeBoundType(Type type, bool physical) {
  std::string rep;
  if (auto data = dyn_cast<DataType>(type)) {
    if (!physical)
      return error("binding-physical-type-at-logical-stage");
    rep = data.getRepresentation().str();
    type = data.getLogical();
  } else if (physical)
    return error("binding-logical-type-at-physical-stage");
  BoundType result;
  if (auto t = dyn_cast<VariantType>(type))
    result = {"variant", t.getDescriptor().drop_front(8).str(), {}};
  else if (type.isSignlessInteger(1))
    result.kind = "bool";
  else if (type.isUnsignedInteger(64))
    result.kind = "index";
  else if (auto t = dyn_cast<FieldType>(type))
    result = {"field", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<MatrixType>(type))
    result = {"matrix", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<MultilinearType>(type))
    result = {"table", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<PointType>(type))
    result = {"point", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<QuadraticType>(type))
    result = {"round", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<GroupType>(type))
    result = {"group", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<UnivariateType>(type))
    result = {"polynomial", t.getDomain().str(), {}};
  else if (auto t = dyn_cast<RankedTensorType>(type)) {
    if (t.getRank() != 1 || !t.isDynamicDim(0) || t.getEncoding())
      return error("binding-type");
    if (t.getElementType().isUnsignedInteger(64))
      result.kind = "indices";
    else if (auto f = dyn_cast<FieldType>(t.getElementType()))
      result = {"vector", f.getDomain().str(), {}};
    else if (auto g = dyn_cast<GroupType>(t.getElementType()))
      result = {"groups", g.getDomain().str(), {}};
    else
      return error("binding-type");
  } else if (auto t = dyn_cast<OracleObjectType>(type))
    result = {t.getKind().str(), t.getScheme().str(), {}};
  else if (auto t = dyn_cast<ObjectType>(type))
    result = {t.getKind().str(), t.getScheme().str(), {}};
  else if (auto t = dyn_cast<CapabilityType>(type)) {
    auto [kind, identity] = t.getKind().split(':');
    result = {kind.str(), identity.str(), {}};
  } else
    return error("binding-type");
  result.representation = std::move(rep);
  auto checked = parseBoundType(result.spelling(), physical);
  if (!checked)
    return checked.takeError();
  if (decodeBoundType(type.getContext(), *checked) !=
      (physical ? Type(DataType::get(type.getContext(), type,
                                     checked->representation))
                : type))
    return error("binding-type-identity");
  return checked;
}

ArrayRef<requirements::Implication> boundCapabilityRules() {
  static const std::vector<requirements::Implication> rules = {
      {"TwoAdicField", "Field"},   {"PrimeField", "Field"},
      {"ExtensionField", "Field"}, {"PairingField", "Field"},
      {"Field", "CommRing"},       {"FieldTranscript", "Transcript"}};
  return rules;
}

ArrayRef<generic::Operation> boundOperationContracts() {
  static const std::vector<generic::Operation> contracts = [] {
    std::vector<generic::Operation> result;
    for (const auto &k : kernels()) {
      // The reference group is an older executable example, not a generic
      // cryptographic group contract. Its existing path remains separate.
      if (k.key.starts_with("group.") || resourceUnitContract(k.key))
        continue;
      generic::Signature sig;
      auto root = [&](StringRef key, StringRef sort, StringRef capability) {
        unsigned index = sig.scope.terms.size();
        sig.scope.terms.push_back({key.str(), {}});
        sig.scope.sorts.push_back(sort.str());
        if (!capability.empty())
          sig.requirements.push_back(
              requirements::Predicate::holds(capability.str(), {index}));
        return index;
      };
      auto project = [&](unsigned parent, StringRef key, StringRef sort) {
        unsigned index = sig.scope.terms.size();
        sig.scope.terms.push_back({key.str(), parent});
        sig.scope.sorts.push_back(sort.str());
        return index;
      };
      std::map<std::string, unsigned> domains;
      auto installField = [&](unsigned f) {
        for (auto kind : {"field", "matrix", "vector", "polynomial", "table",
                          "point", "round", "rng", "nonce"})
          domains[kind] = f;
      };
      if (k.key == "pairing.check") {
        unsigned f = root("F", "Field", "PairingField");
        project(f, "PairingG1", "Group");
        project(f, "PairingG2", "Group");
      } else if (k.key == "field.embed" || k.key == "vector.embed") {
        unsigned e = root("E", "Field", "ExtensionField");
        installField(e);
        project(e, "BaseField", "Field");
      } else if (k.key.starts_with("oracle.") ||
                 k.key.starts_with("commitments.") ||
                 k.key.starts_with("opening_states.")) {
        unsigned c = root("C", "Commitment", "VectorCommitment");
        installField(project(c, "ValueField", "Field"));
        for (auto kind : {"commitment", "proof", "opening_state", "commitments",
                          "opening_states"})
          domains[kind] = c;
      } else if (k.key.starts_with("pcs.")) {
        unsigned c = root("C", "Commitment", "MultilinearOpening");
        installField(project(c, "ValueField", "Field"));
        domains["field"] = project(c, "EvaluationField", "Field");
        domains["point"] = project(c, "PointField", "Field");
        for (auto kind : {"commitment", "proof", "prover_key", "verifier_key",
                          "opening_state"})
          domains[kind] = c;
      } else if (k.key.starts_with("curve.") && k.key != "curve.response") {
        unsigned g = root("G", "Group", "ScalarAction");
        domains["group"] = domains["groups"] = g;
        installField(project(g, "Scalar", "Field"));
      } else if (k.key.starts_with("transcript.")) {
        bool challenge =
            k.key == "transcript.challenge" || k.key == "transcript.draw_index";
        unsigned t = root("T", "Transcript",
                          k.key == "transcript.draw_index" ? "IndexTranscript"
                          : challenge                      ? "FieldTranscript"
                                                           : "Transcript");
        domains["transcript"] = t;
        if (challenge)
          installField(project(t, "ChallengeField", "Field"));
        else {
          StringRef kind =
              k.key.drop_front(StringRef("transcript.observe.").size());
          std::optional<unsigned> payload;
          if (kind == "group" || kind == "groups")
            payload = root("G", "Group", "");
          else if (kind == "commitment" || kind == "commitments" ||
                   kind == "proof")
            payload = root("C", "Commitment", "");
          else if (kind != "bool" && kind != "index" && kind != "indices")
            payload = root("F", "Field", "");
          if (payload)
            domains[kind.str()] = *payload;
          unsigned codec = root("E", "Codec", "");
          std::vector<unsigned> encoded{codec};
          if (payload)
            encoded.push_back(*payload);
          sig.requirements.push_back(requirements::Predicate::holds(
              "Encodes." + kind.str(), std::move(encoded)));
        }
      } else if (k.key != "bool.and" && k.key != "bool.not" &&
                 k.key != "bool.or" && k.key != "control.require" &&
                 !k.key.starts_with("index.") &&
                 !k.key.starts_with("indices.") &&
                 !k.key.starts_with("external.")) {
        installField(root(
            "F", "Field",
            (k.key == "poly.coset_evaluate" ||
             k.key == "poly.coset_interpolate" ||
             k.key == "poly.domain_point" || k.key == "poly.domain_root" ||
             k.key == "poly.domain_points" || k.key == "poly.even_odd_fold" ||
             k.key == "poly.opening_quotient")
                ? "TwoAdicField"
            : k.key == "random.index"    ? "IndexRandomness"
            : k.key.starts_with("poly.") ? "CommRing"
                                         : "Field"));
        if (k.contracts.coset && k.contracts.coset->foldedOutput)
          sig.requirements.push_back(requirements::Predicate::holds(
              "CharacteristicNotTwo", {domains.at("field")}));
      }
      auto type = [&](const std::string &kind) -> generic::Type {
        return {kind, (kind == "bool" || kind == "index" || kind == "indices")
                          ? std::vector<unsigned>{}
                          : std::vector<unsigned>{domains.at(kind)}};
      };
      for (auto [i, t] : enumerate(k.inputs))
        sig.inputs.push_back(
            k.key == "pairing.check" ? generic::Type{t, {unsigned(i + 1)}}
            : (k.key == "field.embed" || k.key == "vector.embed")
                ? generic::Type{t, {1}}
                : type(t));
      for (const auto &t : k.outputs)
        sig.outputs.push_back(type(t));
      result.push_back({k.key.str(), std::move(sig)});
    }
    return result;
  }();
  return contracts;
}

Expected<BoundOperation> resolveBinding(const source::OperationBinding &binding,
                                        bool physical) {
  if (physical && binding.implementation.empty())
    return error("binding-stage");
  if (!physical && !binding.implementation.empty()) {
    // A source may constrain future implementation selection without lowering
    // its logical ports. Validate that exact choice independently here.
    auto selected = resolveBinding(binding, true);
    if (!selected)
      return selected.takeError();
  }
  if (resourceUnitContract(binding.contract)) {
    if (binding.arguments.size() != 1 ||
        !resourceUnitDomain(binding.arguments[0]))
      return error("binding-resource-unit-domain");
    if (physical && binding.implementation != "logical/" + binding.contract)
      return error("binding-implementation");
    BoundType ty{"resource_unit", binding.arguments[0],
                 physical ? "logical.resource_unit/1" : ""};
    std::string operation = binding.contract == "resource_unit.create"
                                ? "pir.resource_unit_create"
                            : binding.contract == "resource_unit.pass"
                                ? "pir.resource_unit_pass"
                                : "pir.resource_unit_consume";
    return BoundOperation{physical ? "plan.kernel" : operation,
                          binding.contract == "resource_unit.create"
                              ? std::vector<BoundType>{}
                              : std::vector<BoundType>{ty},
                          binding.contract == "resource_unit.consume"
                              ? std::vector<BoundType>{}
                              : std::vector<BoundType>{ty}};
  }
  // This is a physical adapter contract, not a generic logical primitive. Its
  // implementation must execute and account for the representation conversion.
  if (binding.contract == "table.relayout") {
    if (!physical || binding.arguments.size() != 3 ||
        installedDomains().identitySort(binding.arguments[0]) != "Field" ||
        binding.implementation != "arkworks/table.relayout")
      return error("binding-conversion");
    auto from = parseBoundType(
        "table:" + binding.arguments[0] + "@" + binding.arguments[1], true);
    if (!from)
      return from.takeError();
    auto to = parseBoundType(
        "table:" + binding.arguments[0] + "@" + binding.arguments[2], true);
    if (!to)
      return to.takeError();
    if (*from == *to)
      return error("binding-conversion");
    return BoundOperation{"plan.kernel", {*from}, {*to}};
  }
  const generic::Signature *signature = nullptr;
  for (const auto &op : boundOperationContracts())
    if (op.name == binding.contract)
      signature = &op.signature;
  if (!signature)
    return error("binding-contract");
  auto identities = resolveStaticArguments(signature->scope, binding.arguments);
  if (!identities)
    return identities.takeError();
  if (auto e = checkClosedRequirements(signature->requirements, *identities))
    return e;
  bool msb = false;
  if (physical) {
    if (auto e = checkImplementation(binding.contract, binding.implementation))
      return e;
    msb = StringRef(binding.implementation).starts_with("arkworks-msb/");
    // This provider is the BLS multilinear implementation, including its
    // table-free round helpers. Sharing arkworks does not extend it to BN254.
    if (msb && binding.arguments != source::Names{"bls12-381.fr"})
      return error("binding-implementation");
    StringRef backend = StringRef(binding.implementation).split('/').first;
    if (backend == "arkworks-msb" || backend == "arkworks-diagonal")
      backend = "arkworks";
    else if (backend == "dalek-diagonal" || backend == "dalek-vartime")
      backend = "dalek";
    if (StringRef(binding.contract).starts_with("transcript.")) {
      const auto &suite = binding.arguments.front();
      if (backendFor(suite) != backend)
        return error("binding-implementation");
      StringRef field = associatedIdentity(suite, "ChallengeField");
      for (const auto &identity : *identities) {
        StringRef sort = installedIdentitySort(identity);
        if (sort == "Codec" || identity == suite)
          continue;
        StringRef payloadField = identity;
        if (sort == "Group")
          payloadField = associatedIdentity(identity, "Scalar");
        else if (sort == "Commitment")
          payloadField = associatedIdentity(identity, "ValueField");
        if (payloadField != field &&
            !(suite == "merlin3.koala-bear.ext8-binomial3.rejection31le/1" &&
              payloadField == "koala-bear"))
          return error("binding-implementation");
      }
    } else {
      for (const auto &identity : *identities) {
        if (installedIdentitySort(identity) == "Codec")
          continue;
        if (backendFor(identity) != backend)
          return error("binding-implementation");
      }
    }
    // Bool-only kernels have one domain-independent installed realization.
    if (identities->empty() &&
        backend != ((StringRef(binding.contract).starts_with("index.") ||
                     StringRef(binding.contract).starts_with("indices.") ||
                     StringRef(binding.contract).starts_with("external."))
                        ? "native"
                        : "arkworks"))
      return error("binding-implementation");
  }
  BoundOperation result;
  for (const auto &k : kernels())
    if (k.key == binding.contract)
      result.operation = k.operation.str();
  auto type = [&](const generic::Type &t) -> Expected<BoundType> {
    BoundType logical{t.constructor,
                      t.arguments.empty() ? "" : (*identities)[t.arguments[0]],
                      ""};
    if (!installedDomains().defaultRepresentation(logical.kind,
                                                  logical.identity))
      return error("binding-representation");
    if (!physical)
      return logical;
    // The existing MSB implementation explicitly selects its table layout.
    // Catalog applicability alone does not establish backend realization.
    if (msb && logical.kind == "table") {
      const auto *rep = installedDomains().representationForLayout(
          logical.kind, logical.identity, "msb");
      if (!rep)
        return error("binding-representation");
      logical.representation = rep->identity;
      return parseBoundType(logical.spelling(), true);
    }
    return defaultRepresentation(logical);
  };
  for (const auto &t : signature->inputs) {
    auto selected = type(t);
    if (!selected)
      return selected.takeError();
    result.inputs.push_back(std::move(*selected));
  }
  for (const auto &t : signature->outputs) {
    auto selected = type(t);
    if (!selected)
      return selected.takeError();
    result.outputs.push_back(std::move(*selected));
  }
  if (physical && StringRef(binding.implementation).contains("-diagonal/")) {
    bool producer = binding.contract == "vector.mul" ||
                    binding.contract == "curve.scale_each";
    auto &port = producer ? result.outputs[0] : result.inputs[1];
    const auto *rep = installedDomains().representationForLayout(
        port.kind, port.identity, "diagonal");
    if (!rep)
      return error("binding-representation");
    port.representation = rep->identity;
  }
  return result;
}

Error checkBindingDeclaration(const source::OperationBinding &binding,
                              bool physical) {
  if (!name(binding.name) || binding.name.find('/') != std::string::npos)
    return error("binding-name");
  if (binding.arguments.size() > 128)
    return error("binding-static-arity");
  // A resource-unit contract's one argument is a slot domain, which its own
  // rule checks.
  if (!resourceUnitContract(binding.contract))
    for (const auto &argument : binding.arguments)
      if (!name(argument))
        return error("binding-static-identity");
  auto resolved = resolveBinding(binding, physical);
  return resolved ? Error::success() : resolved.takeError();
}

} // namespace zkc::protocol
