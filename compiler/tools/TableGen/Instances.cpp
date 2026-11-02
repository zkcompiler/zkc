#include "Instances.h"
#include "Contributions.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using namespace llvm;
namespace {
using Records = std::vector<const Record *>;

void require(bool valid, const Record *r, const Twine &message) {
  if (!valid)
    PrintFatalError(r, message);
}
StringRef text(const Record *r, StringRef field) {
  return r->getValueAsString(field);
}
const Record *nullableDef(const Record *r, StringRef field) {
  const auto *def = dyn_cast<DefInit>(r->getValueInit(field));
  return def ? def->getDef() : nullptr;
}
// A record carries exactly its schema's fields, plus a declared position.
void exactFields(const Record *r, ArrayRef<StringRef> fields) {
  for (const auto &value : r->getValues())
    require(value.getName() == "ordinal" ||
                is_contained(fields, value.getName()),
            r, "unknown field " + value.getName());
}
std::pair<StringRef, StringRef> parameter(const Record *p) {
  return {p->getValueAsDef("kind")->getValueAsString("name"),
          p->getValueAsString("sort")};
}
// The catalog name rule: 1 to 256 characters, a letter or `_` first, then
// letters, digits, `_`, `.`, `-` or `/`.
bool catalogName(StringRef value) {
  return !value.empty() && value.size() <= 256 &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-' || c == '/';
         });
}
bool canonicalDecimal(StringRef value) {
  return !value.empty() && all_of(value, isDigit) &&
         (value.size() == 1 || value.front() != '0');
}
// Both operands are canonical decimals.
bool decimalLess(StringRef left, StringRef right) {
  return left.size() != right.size() ? left.size() < right.size()
                                     : left < right;
}
APInt decimalValue(StringRef value) {
  return APInt(unsigned(value.size() * 4 + 8), value, 10);
}
unsigned decimalBits(StringRef value) {
  return decimalValue(value).getActiveBits();
}
constexpr int64_t staticNaturalLimit = 1048576;

const StringRef frameLayouts[] = {
    "Scalar",     "Vector",      "SparseMatrix",  "MerkleRoot", "MerklePath",
    "DigestRoot", "DigestProof", "PcsCommitment", "PcsProof",   "Table",
    "Sequence",   "Variant",     "FieldArray"};
// Frame fields beyond `tag` that each codec-bearing layout carries.
const std::map<StringRef, std::vector<StringRef>> codecFrameFields = {
    {"Scalar", {"elementBytes"}},
    {"Vector", {"elementBytes"}},
    {"SparseMatrix", {"elementBytes"}},
    {"PcsCommitment", {"bytes"}},
    {"PcsProof", {"bytes", "bytesPerArity"}},
    {"MerkleRoot", {}},
    {"MerklePath", {}},
    {"DigestRoot", {}},
    {"DigestProof", {}},
    {"Table", {}}};
const std::map<StringRef, StringRef> aggregateLayouts = {
    {"sequence", "Sequence"},
    {"variant", "Variant"},
    {"field_array", "FieldArray"}};
// The layout each codec kind's frame uses; commitment and proof frames follow
// their domain's commitment scheme.
const std::map<StringRef, StringRef> kindLayouts = {
    {"field", "Scalar"},   {"group", "Scalar"},  {"bool", "Scalar"},
    {"index", "Scalar"},   {"vector", "Vector"}, {"groups", "Vector"},
    {"indices", "Vector"}, {"bytes", "Vector"},  {"matrix", "SparseMatrix"},
    {"table", "Table"}};
const std::map<std::pair<StringRef, StringRef>, StringRef> schemeLayouts = {
    {{"keccak256Rows", "commitment"}, "MerkleRoot"},
    {{"keccak256Rows", "proof"}, "MerklePath"},
    {{"poseidon2Rows", "commitment"}, "DigestRoot"},
    {{"poseidon2Rows", "proof"}, "DigestProof"},
    {{"multilinearKzg", "commitment"}, "PcsCommitment"},
    {{"multilinearKzg", "proof"}, "PcsProof"}};
const StringRef commitmentSchemes[] = {"keccak256Rows", "poseidon2Rows",
                                       "multilinearKzg"};
// The pinned Poseidon2 instances and the field each one permutes.
const std::map<StringRef, StringRef> permutationFields = {
    {"koala-bear.poseidon2-16", "koala-bear"},
    {"baby-bear.poseidon2-16", "baby-bear"},
    {"goldilocks.poseidon2-8", "goldilocks"}};
const StringRef domainConstructorKinds[] = {
    "Elements",     "Indices",           "Range",
    "Zip",          "Product",           "MatrixRow",
    "MatrixColumn", "MatrixCoordinates", "SourceArray"};
const StringRef providerNames[] = {
    "arkworks", "blst", "dalek", "halo2curves-axiom", "plonky3", "spongefish"};
const StringRef unitNames[] = {"arkworks",    "blst",    "dalek",
                               "halo2curves", "plonky3", "independent"};
// The provider units the native-installation chapter states explicitly.
const std::map<StringRef, StringRef> statedProviderUnits = {
    {"spongefish", "arkworks"}, {"halo2curves-axiom", "halo2curves"}};

std::vector<std::pair<StringRef, StringRef>> memberPairs(const Record *row) {
  std::vector<std::pair<StringRef, StringRef>> result;
  for (const auto *element :
       row->getValueAsListInit("members")->getElements()) {
    const auto *pair = dyn_cast<ListInit>(element);
    require(pair && pair->size() == 2, row,
            "domain member is a [member, identity] pair");
    const auto *member = dyn_cast<StringInit>(pair->getElement(0));
    const auto *identity = dyn_cast<StringInit>(pair->getElement(1));
    require(member && identity, row,
            "domain member is a [member, identity] pair");
    result.emplace_back(member->getValue(), identity->getValue());
  }
  return result;
}

/// The declarations' installed-instance tables, resolved by declared identity
/// and checked against the declared sorts, types, members and capabilities.
class Logical {
public:
  explicit Logical(const RecordKeeper &records);

  DeclarationOrder order;
  Records domains, logicalTypes, frameTags, codecs, aggregateFrames, services,
      limits, finiteDefinitions, domainConstructors;
  std::map<std::string, const Record *> domainRows, codecRows, typeRows,
      capabilityRows, operationRows;
  std::set<std::pair<std::string, std::string>> instances;
  std::map<std::pair<std::string, std::string>, const Record *> codecByPair;
  std::map<int64_t, const Record *> tags;
  // (constructor, field) of each aggregate frame row.
  std::set<std::pair<std::string, std::string>> aggregates;

  const Record *type(StringRef name) const {
    auto found = typeRows.find(name.str());
    return found == typeRows.end() ? nullptr : found->second;
  }
  const Record *domain(StringRef identity) const {
    auto found = domainRows.find(identity.str());
    return found == domainRows.end() ? nullptr : found->second;
  }
  std::optional<StringRef> member(const Record *row, StringRef name) const {
    for (auto [member, identity] : memberPairs(row))
      if (member == name)
        return identity;
    return std::nullopt;
  }
  // The Field facts of a declared Field domain.
  const Record *fieldRow(StringRef identity, const Record *context) const {
    const auto *row = domain(identity);
    require(row && text(row, "sort") == "Field", context,
            identity + " is not a Field domain");
    return row;
  }
  const Record *facts(const Record *fieldRow) const {
    return fieldRow->getValueAsDef("fieldFacts");
  }
  const Record *structure(const Record *fieldRow) const {
    return facts(fieldRow)->getValueAsDef("structure");
  }
  // Rows along BaseField extensions, starting at `row`; cycles refuse.
  Records baseChain(const Record *row) const {
    Records chain{row};
    while (true) {
      const auto *shape = structure(chain.back());
      if (text(shape, "kind") != "extension" ||
          text(shape, "over") != "BaseField")
        return chain;
      auto base = member(chain.back(), "BaseField");
      require(base.has_value(), chain.back(),
              "BaseField extension requires its BaseField member");
      const auto *next = fieldRow(*base, chain.back());
      require(!is_contained(chain, next), row, "cyclic BaseField extension");
      chain.push_back(next);
    }
  }
  const Record *primeBase(const Record *row) const {
    const auto *last = baseChain(row).back();
    return text(structure(last), "kind") == "prime" ? last : nullptr;
  }
  // The coset convention of a row, or of its prime base for an extension.
  const Record *convention(const Record *row) const {
    for (const auto *link : baseChain(row))
      if (const auto *twoAdic = nullableDef(facts(link), "twoAdic"))
        return twoAdic;
    return nullptr;
  }
  // Canonical element bytes derived from the structure, if the structure
  // determines them.
  std::optional<int64_t> elementWidth(const Record *row) const {
    const auto *shape = structure(row);
    auto characteristic = text(facts(row), "characteristic");
    if (text(shape, "kind") == "prime") {
      auto largest = decimalValue(characteristic);
      largest -= 1;
      return int64_t((largest.getActiveBits() + 7) / 8);
    }
    if (text(shape, "over") == "BaseField") {
      auto base = elementWidth(fieldRow(*member(row, "BaseField"), row));
      // A width beyond the count bound matches no declared elementBytes.
      if (!base || *base > staticNaturalLimit / shape->getValueAsInt("degree"))
        return std::nullopt;
      return shape->getValueAsInt("degree") * *base;
    }
    if (characteristic == "2" && shape->getValueAsInt("degree") % 8 == 0)
      return shape->getValueAsInt("degree") / 8;
    return std::nullopt;
  }
  // Exact domain arguments name declared domain rows of their sort.
  bool resolves(StringRef sort, StringRef identity) const {
    const auto *row = domain(identity);
    return row && text(row, "sort") == sort;
  }

private:
  std::set<std::string> sorts;
  std::map<std::tuple<std::string, std::string, std::string>, const Record *>
      members;
  std::vector<std::pair<std::string, std::string>> rules;
  void checkDomains();
  void checkDomainFacts(const Record *row, std::set<std::string> &conventions);
  void checkTypes();
  void checkCodecs();
  void checkFrameUsers();
  void checkSourceTables();
};

Logical::Logical(const RecordKeeper &records)
    : order(records), domains(order.sort("ZKC_InstalledDomain")),
      logicalTypes(order.sort("ZKC_LogicalTypeInstance")),
      frameTags(order.sort("ZKC_FrameTag")), codecs(order.sort("ZKC_Codec")),
      aggregateFrames(order.sort("ZKC_AggregateFrame")),
      services(order.sort("ZKC_RandomService")),
      limits(order.sort("ZKC_Limit")),
      finiteDefinitions(order.sort("ZKC_FiniteDefinition")),
      domainConstructors(order.sort("ZKC_DomainConstructor")) {
  for (const auto *sort : order.sort("ZKC_Sort"))
    sorts.insert(text(sort, "name").str());
  for (const auto *type : order.sort("ZKC_Type"))
    typeRows.emplace(text(type, "name").str(), type);
  for (const auto *capability : order.sort("ZKC_Capability"))
    capabilityRows.emplace(text(capability, "name").str(), capability);
  for (const auto *operation : order.sort("ZKC_Operation"))
    operationRows.emplace(text(operation, "name").str(), operation);
  for (const auto *member : order.sort("ZKC_Member")) {
    auto [kind, sort] = parameter(member->getValueAsDef("owner"));
    members.emplace(
        std::make_tuple(kind.str(), sort.str(), text(member, "name").str()),
        member);
  }
  for (const auto *rule : order.sort("ZKC_Implication"))
    rules.emplace_back(text(rule->getValueAsDef("premise"), "name").str(),
                       text(rule->getValueAsDef("conclusion"), "name").str());
  checkDomains();
  checkTypes();
  checkCodecs();
  checkFrameUsers();
  checkSourceTables();
}

void Logical::checkDomains() {
  for (const auto *row : domains) {
    exactFields(row, {"identity", "sort", "members", "capabilities",
                      "fieldFacts", "transcriptFacts", "commitmentFacts"});
    auto identity = text(row, "identity");
    require(catalogName(identity), row, "invalid catalog identity");
    require(domainRows.emplace(identity.str(), row).second, row,
            "duplicate domain identity");
  }
  for (const auto *row : codecs) {
    exactFields(row, {"identity", "kind", "domain", "frame"});
    auto identity = text(row, "identity");
    require(catalogName(identity), row, "invalid catalog identity");
    require(!domainRows.count(identity.str()) &&
                codecRows.emplace(identity.str(), row).second,
            row, "duplicate identity across domains and codecs");
  }
  std::set<std::string> conventions;
  for (const auto *row : domains) {
    auto sort = text(row, "sort");
    require(sorts.count(sort.str()) && sort != "Codec" && sort != "Slot", row,
            "invalid domain sort");
    require(row->isValueUnset("fieldFacts") == (sort != "Field") &&
                row->isValueUnset("transcriptFacts") ==
                    (sort != "Transcript") &&
                row->isValueUnset("commitmentFacts") == (sort != "Commitment"),
            row, "domain facts disagree with its sort");
    std::map<StringRef, StringRef> named;
    for (auto [name, target] : memberPairs(row)) {
      auto found = members.find(
          std::make_tuple(std::string("Domain"), sort.str(), name.str()));
      require(found != members.end(), row,
              name + " is not a member of sort " + sort);
      require(named.emplace(name, target).second, row,
              "duplicate domain member");
      auto [kind, resultSort] =
          parameter(found->second->getValueAsDef("result"));
      const auto *resolved = domain(target);
      require(kind == "Domain" && resolved &&
                  text(resolved, "sort") == resultSort,
              row, "domain member sort mismatch");
    }
    auto capabilities = row->getValueAsListOfStrings("capabilities");
    std::set<StringRef> held;
    for (auto name : capabilities) {
      require(held.insert(name).second, row, "duplicate capability fact");
      auto found = capabilityRows.find(name.str());
      bool unary = false;
      if (found != capabilityRows.end()) {
        auto ps = found->second->getValueAsListOfDefs("parameters");
        unary = ps.size() == 1 &&
                parameter(ps[0]) == std::make_pair(StringRef("Domain"), sort);
      }
      require(unary, row, name + " is not a unary predicate over " + sort);
    }
    for (const auto &[premise, conclusion] : rules)
      require(!held.count(premise) || held.count(conclusion), row,
              "capabilities are not closed under rules");
    if (held.count("PairingField")) {
      std::vector<StringRef> groups;
      for (auto name : {"PairingG1", "PairingG2", "PairingGT"})
        if (named.count(name))
          groups.push_back(named.at(name));
      require(named.count("PairingG1") && named.count("PairingG2") &&
                  std::set<StringRef>(groups.begin(), groups.end()).size() ==
                      groups.size(),
              row, "pairing field requires distinct pairing groups");
      for (auto group : groups) {
        const auto *target = domain(group);
        require(is_contained(target->getValueAsListOfStrings("capabilities"),
                             "ScalarAction") &&
                    member(target, "Scalar") == text(row, "identity"),
                row, "pairing group must act with this field as Scalar");
      }
    }
    require(held.count("PairingField") ||
                (!named.count("PairingG1") && !named.count("PairingG2") &&
                 !named.count("PairingGT")),
            row, "pairing group members occur only on PairingField rows");
    if (named.count("PointField") || named.count("EvaluationField"))
      require(sort == "Commitment" &&
                  text(row->getValueAsDef("commitmentFacts"), "scheme") ==
                      "multilinearKzg",
              row,
              "PointField and EvaluationField occur only on multilinear KZG "
              "commitments");
    checkDomainFacts(row, conventions);
  }
  // Conventions follow BaseField chains: check them once all facts are known.
  for (const auto *row : domains)
    if (text(row, "sort") == "Field")
      require(is_contained(row->getValueAsListOfStrings("capabilities"),
                           "TwoAdicField") == bool(convention(row)),
              row, "TwoAdicField disagrees with the coset convention");
}

void Logical::checkDomainFacts(const Record *row,
                               std::set<std::string> &conventions) {
  auto sort = text(row, "sort");
  auto capabilities = row->getValueAsListOfStrings("capabilities");
  auto holds = [&](StringRef name) { return is_contained(capabilities, name); };
  if (sort == "Field") {
    const auto *facts = row->getValueAsDef("fieldFacts");
    exactFields(facts, {"characteristic", "structure", "twoAdic"});
    auto characteristic = text(facts, "characteristic");
    require(canonicalDecimal(characteristic) && characteristic.size() <= 1024 &&
                characteristic != "0" && characteristic != "1",
            row, "invalid characteristic");
    require(holds("CharacteristicNotTwo") == (characteristic != "2"), row,
            "CharacteristicNotTwo disagrees with the characteristic");
    const auto *shape = facts->getValueAsDef("structure");
    exactFields(shape, {"kind", "over", "degree", "reduction"});
    auto kind = text(shape, "kind");
    require(kind == "prime" || kind == "extension", row,
            "unknown field structure");
    const bool prime = kind == "prime";
    require(prime ==
                (shape->isValueUnset("over") && shape->isValueUnset("degree") &&
                 shape->isValueUnset("reduction")),
            row, "field structure fields disagree with its kind");
    require(holds("PrimeField") == prime, row,
            "PrimeField disagrees with the structure");
    // Rows over BaseField are exactly the rows holding ExtensionField.
    const bool overBase = !prime && text(shape, "over") == "BaseField";
    require(holds("ExtensionField") == overBase, row,
            "ExtensionField disagrees with the structure");
    require(member(row, "BaseField").has_value() == overBase, row,
            "exactly the rows over BaseField have a BaseField member");
    if (!prime) {
      auto over = text(shape, "over");
      require(over == "BaseField" || over == "PrimeSubfield", row,
              "unknown extension base");
      const auto degree = shape->getValueAsInt("degree");
      require(degree >= 2 && degree <= staticNaturalLimit, row,
              "extension degree is at least 2");
      require(!shape->getValueAsListOfDefs("reduction").empty(), row,
              "extension reduction is a nonempty list");
      int64_t previous = -1;
      for (const auto *term : shape->getValueAsListOfDefs("reduction")) {
        exactFields(term, {"exponent", "coefficient"});
        const auto exponent = term->getValueAsInt("exponent");
        auto coefficient = text(term, "coefficient");
        require(exponent >= 0 && (previous < 0 || exponent < previous), row,
                "reduction exponents must strictly decrease");
        require(exponent < degree, row,
                "reduction exponent reaches the degree");
        require(canonicalDecimal(coefficient) && coefficient != "0" &&
                    decimalLess(coefficient, characteristic),
                row,
                "reduction coefficient must be a nonzero prime-subfield "
                "element");
        previous = exponent;
      }
      if (overBase) {
        auto base = member(row, "BaseField");
        require(base.has_value(), row,
                "BaseField extension requires its BaseField member");
        require(text(this->facts(fieldRow(*base, row)), "characteristic") ==
                    characteristic,
                row, "BaseField has another characteristic");
      }
    }
    if (const auto *twoAdic = nullableDef(facts, "twoAdic")) {
      exactFields(twoAdic,
                  {"convention", "maximalRoot", "twoAdicity", "ordering"});
      require(prime, row, "a two-adic convention belongs to a prime row");
      auto root = text(twoAdic, "maximalRoot");
      const auto adicity = twoAdic->getValueAsInt("twoAdicity");
      require(adicity >= 1 && adicity <= 64, row,
              "two-adicity is between 1 and 64");
      require(canonicalDecimal(root) && decimalLess(root, characteristic), row,
              "maximal root is not a field element");
      require(text(twoAdic, "ordering") == "powers", row,
              "unknown coset ordering");
      auto convention = text(twoAdic, "convention");
      require(catalogName(convention) &&
                  conventions.insert(convention.str()).second,
              row, "invalid or duplicate coset convention");
    }
  } else if (sort == "Transcript") {
    const auto *facts = row->getValueAsDef("transcriptFacts");
    exactFields(facts, {"family", "hash", "decoder", "bindsSuite"});
    auto family = text(facts, "family");
    auto decoder = text(facts, "decoder");
    require(family == "merlin3" || family == "spongefish0.8.0" ||
                family == "hash-chain",
            row, "unknown transcript family");
    require(decoder == "fr64be" || decoder == "rejection31le" ||
                decoder == "rejection64le" || decoder == "scalar64le",
            row, "unknown challenge decoder");
    const bool chain = family == "hash-chain";
    require(chain ? !facts->isValueUnset("hash") &&
                        text(facts, "hash") == "keccak256"
                  : facts->isValueUnset("hash"),
            row, "keccak256 hash exactly for hash-chain suites");
    require(holds("Transcript") && holds("FieldTranscript"), row,
            "transcript row requires Transcript and FieldTranscript");
    auto challenge = member(row, "ChallengeField");
    require(challenge.has_value(), row,
            "transcript row requires ChallengeField");
    const auto *field = fieldRow(*challenge, row);
    if (decoder == "fr64be" || decoder == "scalar64le")
      require(text(structure(field), "kind") == "prime", row,
              decoder + " requires a prime challenge field");
    if (decoder == "rejection31le" || decoder == "rejection64le")
      require(decimalBits(text(this->facts(field), "characteristic")) <=
                  (decoder == "rejection31le" ? 31u : 64u),
              row, decoder + " challenge characteristic is too large");
  } else if (sort == "Commitment") {
    const auto *facts = row->getValueAsDef("commitmentFacts");
    exactFields(facts,
                {"scheme", "digestBytes", "permutation", "digestWordBytes"});
    auto scheme = text(facts, "scheme");
    require(is_contained(commitmentSchemes, scheme), row,
            "unknown commitment scheme");
    require(
        facts->isValueUnset("digestBytes") == (scheme == "multilinearKzg") &&
            facts->isValueUnset("permutation") == (scheme != "poseidon2Rows") &&
            facts->isValueUnset("digestWordBytes") ==
                (scheme != "poseidon2Rows"),
        row, "commitment fields disagree with its scheme");
    require(member(row, "ValueField").has_value(), row,
            "commitment row requires ValueField");
    if (scheme != "multilinearKzg")
      require(facts->getValueAsInt("digestBytes") == 32, row,
              "row commitments have 32-byte digests");
    if (scheme == "poseidon2Rows") {
      auto found = permutationFields.find(text(facts, "permutation"));
      require(found != permutationFields.end(), row,
              "unknown Poseidon2 permutation");
      auto value = *member(row, "ValueField");
      const auto *base = primeBase(fieldRow(value, row));
      require(found->second == value ||
                  (base && found->second == text(base, "identity")),
              row,
              "permutation field is not the value field or its prime base");
    }
  }
}

void Logical::checkTypes() {
  for (const auto *row : logicalTypes) {
    exactFields(row, {"kind", "domain"});
    auto kind = text(row, "kind"), identity = text(row, "domain");
    const auto *declared = type(kind);
    require(declared && kind != "variant" && kind != "resource_unit", row,
            "invalid logical type constructor " + kind);
    auto ps = declared->getValueAsListOfDefs("parameters");
    if (ps.empty())
      require(identity.empty(), row, "a nullary instance has the empty domain");
    else {
      const auto *target = domain(identity);
      require(ps.size() == 1 && parameter(ps[0]).first == "Domain" && target &&
                  text(target, "sort") == parameter(ps[0]).second,
              row, "invalid logical type instance " + kind + " " + identity);
    }
    require(instances.emplace(kind.str(), identity.str()).second, row,
            "duplicate logical type instance");
    if (!declared->isValueUnset("setup")) {
      const auto *target = domain(identity);
      require(target && text(target, "sort") == "Commitment" &&
                  text(target->getValueAsDef("commitmentFacts"), "scheme") ==
                      "multilinearKzg",
              row, "setup keys exist only over multilinear KZG commitments");
    }
  }
}

void Logical::checkCodecs() {
  for (const auto *row : frameTags) {
    exactFields(row, {"tag", "layout", "shared"});
    const auto tag = row->getValueAsInt("tag");
    require(tag >= 1 && tag <= 255 && tags.emplace(tag, row).second, row,
            "invalid or duplicate frame tag");
    require(is_contained(frameLayouts, text(row, "layout")), row,
            "unknown frame layout");
    if (const auto *shared = nullableDef(row, "shared")) {
      exactFields(shared, {"kind", "scheme"});
      require(type(text(shared, "kind")) &&
                  is_contained(commitmentSchemes, text(shared, "scheme")),
              row, "shared frame names an undeclared kind or scheme");
    }
  }
  for (const auto *row : codecs) {
    auto kind = text(row, "kind"), identity = text(row, "domain");
    require(instances.count({kind.str(), identity.str()}), row,
            "codec payload is not an admitted logical type");
    require(codecByPair.emplace(std::make_pair(kind.str(), identity.str()), row)
                .second,
            row, "second codec for one logical type");
    std::vector<std::pair<StringRef, StringRef>> expected{{"Domain", "Codec"}};
    if (!identity.empty())
      expected.emplace_back("Domain", text(domain(identity), "sort"));
    auto predicate = capabilityRows.find(("Encodes." + kind).str());
    bool encodes = false;
    if (predicate != capabilityRows.end()) {
      auto ps = predicate->second->getValueAsListOfDefs("parameters");
      encodes = ps.size() == expected.size() &&
                all_of(zip(ps, expected), [](const auto &pair) {
                  return parameter(std::get<0>(pair)) == std::get<1>(pair);
                });
    }
    require(encodes, row,
            "codec kind " + kind + " lacks its Encodes predicate");
    const bool message = type(kind)->getValueAsBit("message");
    const auto *frame = nullableDef(row, "frame");
    if (!frame) {
      require(!message, row, "a message codec requires a frame");
      continue;
    }
    auto found = tags.find(frame->getValueAsInt("tag"));
    require(found != tags.end(), row, "codec frame names an undeclared tag");
    auto layout = text(found->second, "layout");
    require(message || layout == "Table", row,
            "only the input-only table frame may serve a non-message codec");
    auto fields = codecFrameFields.find(layout);
    require(fields != codecFrameFields.end(), row,
            "layout " + layout + " carries no codec frame");
    // The codec's kind fixes its frame layout; commitment and proof frames
    // follow the scheme of their commitment domain.
    StringRef fixedLayout;
    if (auto fixed = kindLayouts.find(kind); fixed != kindLayouts.end())
      fixedLayout = fixed->second;
    else if (const auto *target = domain(identity);
             target && text(target, "sort") == "Commitment") {
      auto scheme = text(target->getValueAsDef("commitmentFacts"), "scheme");
      if (auto byScheme = schemeLayouts.find({scheme, kind});
          byScheme != schemeLayouts.end())
        fixedLayout = byScheme->second;
    }
    require(layout == fixedLayout, row,
            "codec kind " + kind + " fixes its frame layout");
    exactFields(frame, {"tag", "elementBytes", "bytes", "bytesPerArity"});
    std::vector<StringRef> allowed{"tag"};
    append_range(allowed, fields->second);
    for (auto field : {"elementBytes", "bytes", "bytesPerArity"})
      require(frame->isValueUnset(field) != is_contained(allowed, field), row,
              "frame fields disagree with the tag layout");
    for (auto field : {"elementBytes", "bytes", "bytesPerArity"})
      if (!frame->isValueUnset(field))
        require(frame->getValueAsInt(field) >= 0 &&
                    frame->getValueAsInt(field) <= staticNaturalLimit,
                row, StringRef(field) + " is a declaration count");
    if (kind == "field" || kind == "vector" || kind == "matrix") {
      auto width = elementWidth(fieldRow(identity, row));
      require(width && !frame->isValueUnset("elementBytes") &&
                  frame->getValueAsInt("elementBytes") == *width,
              row,
              text(row, "identity") +
                  " element width disagrees with the field structure");
    }
  }
  for (const auto &[pair, row] : codecByPair) {
    if (pair.first != "group")
      continue;
    auto many = codecByPair.find({"groups", pair.second});
    if (many == codecByPair.end())
      continue;
    const auto *single = nullableDef(row, "frame");
    const auto *vector = nullableDef(many->second, "frame");
    if (!single || !vector)
      continue;
    require(!single->isValueUnset("elementBytes") &&
                !vector->isValueUnset("elementBytes") &&
                single->getValueAsInt("elementBytes") ==
                    vector->getValueAsInt("elementBytes"),
            row, "group and groups codecs disagree on elementBytes");
  }
  // Poseidon2 digest words take the permutation field's codec width.
  for (const auto *row : domains) {
    if (text(row, "sort") != "Commitment")
      continue;
    const auto *facts = row->getValueAsDef("commitmentFacts");
    if (text(facts, "scheme") != "poseidon2Rows")
      continue;
    auto field = permutationFields.at(text(facts, "permutation"));
    auto scalar = codecByPair.find({"field", field.str()});
    const auto *frame = scalar == codecByPair.end()
                            ? nullptr
                            : nullableDef(scalar->second, "frame");
    require(frame && !frame->isValueUnset("elementBytes") &&
                frame->getValueAsInt("elementBytes") ==
                    facts->getValueAsInt("digestWordBytes"),
            row,
            "digest word width disagrees with the permutation field's codec "
            "frame");
  }
}

void Logical::checkFrameUsers() {
  std::map<int64_t, Records> users;
  for (const auto *row : codecs)
    if (const auto *frame = nullableDef(row, "frame"))
      users[frame->getValueAsInt("tag")].push_back(row);
  for (const auto *row : aggregateFrames) {
    exactFields(row, {"constructor", "domain", "tag"});
    auto constructor = text(row, "constructor"), identity = text(row, "domain");
    auto layout = aggregateLayouts.find(constructor);
    require(layout != aggregateLayouts.end(), row,
            "no aggregate frame for " + constructor);
    if (constructor == "field_array") {
      fieldRow(identity, row);
      auto scalar = codecByPair.find({"field", identity.str()});
      const auto *frame = scalar == codecByPair.end()
                              ? nullptr
                              : nullableDef(scalar->second, "frame");
      require(frame && !frame->isValueUnset("elementBytes"), row,
              "field_array frame requires the field's scalar frame");
    } else
      require(identity.empty(), row,
              constructor + " frame has the empty domain");
    require(aggregates.emplace(constructor.str(), identity.str()).second, row,
            "duplicate aggregate frame");
    auto tag = tags.find(row->getValueAsInt("tag"));
    require(tag != tags.end() && text(tag->second, "layout") == layout->second,
            row, "aggregate frame tag layout mismatch");
    users[tag->first].push_back(row);
  }
  for (const auto &[number, tag] : tags) {
    const auto &used = users[number];
    const auto *shared = nullableDef(tag, "shared");
    if (!shared) {
      require(used.size() == 1, tag,
              "frame tag " + Twine(number) + " needs exactly one user");
      continue;
    }
    std::set<const Record *> expected;
    for (const auto *codec : codecs) {
      const auto *target = domain(text(codec, "domain"));
      if (text(codec, "kind") == text(shared, "kind") && target &&
          text(target, "sort") == "Commitment" &&
          text(target->getValueAsDef("commitmentFacts"), "scheme") ==
              text(shared, "scheme"))
        expected.insert(codec);
    }
    require(std::set<const Record *>(used.begin(), used.end()) == expected &&
                expected.size() >= 2 && used.size() == expected.size(),
            tag,
            "shared frame tag " + Twine(number) +
                " users disagree with its kind and scheme");
  }
}

void Logical::checkSourceTables() {
  std::set<std::string> contracts, fields, rng;
  for (const auto &[kind, identity] : instances)
    if (kind == "rng")
      rng.insert(identity);
  for (const auto *row : services) {
    exactFields(row, {"contract", "fieldDomain"});
    auto contract = text(row, "contract"), field = text(row, "fieldDomain");
    require(catalogName(contract) && contracts.insert(contract.str()).second,
            row, "invalid or duplicate random service contract");
    fieldRow(field, row);
    require(fields.insert(field.str()).second, row,
            "duplicate random service field");
  }
  if (fields != rng)
    PrintFatalError("random services and rng logical types disagree");
  const StringRef units[] = {"roles", "bytes", "elements", "entries", "steps"};
  const StringRef phases[] = {"formation", "admission", "publication",
                              "execution"};
  std::set<std::string> names;
  for (const auto *row : limits) {
    exactFields(row, {"name", "value", "unit", "owner", "scope", "phase"});
    auto name = text(row, "name");
    require(catalogName(name) && names.insert(name.str()).second, row,
            "invalid or duplicate limit");
    require(row->getValueAsInt("value") >= 0, row, "invalid limit value");
    require(is_contained(units, text(row, "unit")) &&
                is_contained(phases, text(row, "phase")),
            row, "unknown limit unit or phase");
    require(!text(row, "owner").empty() && !text(row, "scope").empty(), row,
            "limit owner and scope are named");
  }
  std::set<std::string> identities;
  for (const auto *row : finiteDefinitions) {
    exactFields(row,
                {"identity", "mode", "operation", "collection", "filtered"});
    auto identity = text(row, "identity");
    require(catalogName(identity) && identities.insert(identity.str()).second,
            row, "invalid or duplicate finite definition");
    auto mode = text(row, "mode"), operation = text(row, "operation");
    require((mode == "math" || mode == "local") &&
                (operation == "fold" || operation == "collect"),
            row, "unknown finite definition mode or operation");
    const bool fold = operation == "fold";
    require(fold == row->isValueUnset("collection"), row,
            "only collect names a collection");
    if (!fold) {
      auto collection = text(row, "collection");
      require(collection == "vector" || collection == "groups" ||
                  collection == "sequence" || collection == "indices" ||
                  collection == "field_array",
              row, "unknown finite collection");
      require(!(collection == "field_array" && row->getValueAsBit("filtered")),
              row, "field_array collection cannot be filtered");
    }
  }
  identities.clear();
  for (const auto *row : domainConstructors) {
    exactFields(row, {"identity", "kind", "axis"});
    auto identity = text(row, "identity");
    require(catalogName(identity) && identities.insert(identity.str()).second,
            row, "invalid or duplicate domain constructor");
    require(is_contained(domainConstructorKinds, text(row, "kind")), row,
            "unknown domain constructor kind");
    const auto axis = row->getValueAsInt("axis");
    require(axis == 0 || axis == 1, row, "domain constructor axis is 0 or 1");
  }
}

/// The native installation, resolved against its declaration records.
class Physical {
public:
  Physical(const RecordKeeper &records, const Logical &logical);

  const Logical &logical;
  Records representations, applied, providers, providerUnits, fieldForms,
      physicalArguments;

private:
  std::map<std::tuple<std::string, std::string, std::string>, const Record *>
      keys;
  std::map<std::pair<std::string, std::string>, const Record *> defaults;
  std::map<std::string, const Record *> providerRows;
  std::map<std::string, std::string> units;
  static Records rows(const RecordKeeper &records, StringRef category);
  // Whether the instance has a codec with a frame; the input-only table
  // codec counts.
  bool framed(StringRef kind, StringRef domain) const {
    auto found = logical.codecByPair.find({kind.str(), domain.str()});
    return found != logical.codecByPair.end() &&
           nullableDef(found->second, "frame");
  }
  void checkProviders();
  void checkRepresentations();
  void checkApplied();
  void checkFieldForms();
  void typeTree(const Record *owner, const Record *tree) const;
};

// Installation rows join no contribution; their declared position orders them.
Records Physical::rows(const RecordKeeper &records, StringRef category) {
  Records result = records.getAllDerivedDefinitionsIfDefined(category);
  std::set<int64_t> ordinals;
  for (const auto *row : result)
    require(row->getValue("ordinal") &&
                ordinals.insert(row->getValueAsInt("ordinal")).second,
            row, "installation row requires a unique declared position");
  stable_sort(result, [](const Record *a, const Record *b) {
    return a->getValueAsInt("ordinal") < b->getValueAsInt("ordinal");
  });
  return result;
}

Physical::Physical(const RecordKeeper &records, const Logical &logical)
    : logical(logical),
      representations(rows(records, "ZKC_NativeRepresentation")),
      applied(rows(records, "ZKC_AppliedRepresentation")),
      providers(rows(records, "ZKC_ProviderPreference")),
      providerUnits(rows(records, "ZKC_ProviderUnit")),
      fieldForms(rows(records, "ZKC_FieldForm")),
      physicalArguments(rows(records, "ZKC_PhysicalArguments")) {
  checkProviders();
  checkRepresentations();
  checkApplied();
  checkFieldForms();
  std::set<std::string> operations;
  for (const auto *row : physicalArguments) {
    exactFields(row, {"operation"});
    auto operation = text(row, "operation");
    require(logical.operationRows.count(operation.str()), row,
            "physical argument row names an undeclared operation");
    require(operations.insert(operation.str()).second, row,
            "duplicate physical argument row");
  }
}

void Physical::checkProviders() {
  for (const auto *row : providers) {
    exactFields(row, {"domain", "provider", "alternatives"});
    auto identity = text(row, "domain");
    require(logical.domain(identity), row,
            "provider row names an undeclared domain");
    require(providerRows.emplace(identity.str(), row).second, row,
            "duplicate provider row");
    std::set<StringRef> named{text(row, "provider")};
    for (auto alternative : row->getValueAsListOfStrings("alternatives"))
      require(named.insert(alternative).second, row,
              "provider appears twice in one row");
    for (auto name : named)
      require(is_contained(providerNames, name), row, "unknown provider");
  }
  for (const auto *domain : logical.domains)
    require(providerRows.count(text(domain, "identity").str()), domain,
            "every domain has exactly one provider row");
  for (const auto *row : providerUnits) {
    exactFields(row, {"provider", "unit"});
    auto provider = text(row, "provider"), unit = text(row, "unit");
    require(is_contained(providerNames, provider) &&
                is_contained(unitNames, unit) && unit != "independent",
            row, "invalid provider unit");
    require(units.emplace(provider.str(), unit.str()).second, row,
            "duplicate provider unit");
  }
  for (auto provider : providerNames)
    if (!units.count(provider.str()))
      PrintFatalError("every provider has exactly one unit: " + provider);
  for (const auto &[provider, unit] : statedProviderUnits)
    if (units.at(provider.str()) != unit)
      PrintFatalError(provider + " is installed by " + unit);
}

void Physical::checkRepresentations() {
  std::set<std::tuple<std::string, std::string, std::string>> layouts;
  for (const auto *row : representations) {
    exactFields(row, {"identity", "kind", "domain", "isDefault", "layout",
                      "frame", "unit"});
    auto identity = text(row, "identity"), kind = text(row, "kind"),
         domain = text(row, "domain"), layout = text(row, "layout");
    require(catalogName(identity), row, "invalid representation identity");
    require(logical.instances.count({kind.str(), domain.str()}), row,
            "representation names an undeclared logical type instance");
    require(
        keys.emplace(std::make_tuple(kind.str(), domain.str(), identity.str()),
                     row)
            .second,
        row, "duplicate representation");
    if (row->getValueAsBit("isDefault"))
      require(defaults.emplace(std::make_pair(kind.str(), domain.str()), row)
                  .second,
              row, "second default representation");
    if (!layout.empty())
      require(
          catalogName(layout) &&
              layouts.emplace(kind.str(), domain.str(), layout.str()).second,
          row, "invalid or duplicate representation layout");
    require(text(row, "frame") == "canonical" || text(row, "frame") == "local",
            row, "unknown representation frame");
    require(text(row, "frame") == "local" || framed(kind, domain), row,
            "a canonical representation requires a framed codec for its "
            "instance");
    require(is_contained(unitNames, text(row, "unit")), row,
            "unknown installation unit");
  }
  for (const auto &[kind, domain] : logical.instances)
    if (!defaults.count({kind, domain}))
      PrintFatalError("logical type instance has no default representation: " +
                      kind + " " + domain);
  for (const auto &[instance, row] : defaults) {
    if (framed(instance.first, instance.second))
      require(text(row, "frame") == "canonical", row,
              "the default of a framed instance is canonical");
    // Default storage belongs to the unit of the domain's default provider;
    // instances without a domain are provider-free logical storage.
    StringRef expected = "independent";
    if (!instance.second.empty())
      expected =
          units.at(text(providerRows.at(instance.second), "provider").str());
    require(text(row, "unit") == expected, row,
            "default storage unit disagrees with the default provider");
  }
}

// An exact Type pattern names an admitted logical type instance: a nullary
// application or one over a single declared domain.
void Physical::typeTree(const Record *owner, const Record *tree) const {
  exactFields(tree, {"constructor", "arguments"});
  auto constructor = text(tree, "constructor");
  auto arguments = tree->getValueAsListOfDefs("arguments");
  std::string identity;
  if (!arguments.empty()) {
    require(arguments.size() == 1 && text(arguments[0], "kind") == "domain",
            owner, "type pattern is not a logical type instance");
    exactFields(arguments[0], {"kind", "sort", "identity"});
    require(logical.resolves(text(arguments[0], "sort"),
                             text(arguments[0], "identity")),
            owner, "domain argument disagrees with its parameter");
    identity = text(arguments[0], "identity").str();
  }
  require(logical.instances.count({constructor.str(), identity}), owner,
          "type pattern is not a logical type instance");
}

bool overlaps(const Record *left, const Record *right) {
  auto a = text(left, "kind"), b = text(right, "kind");
  if (a == "any" || b == "any")
    return true;
  if (a != b)
    return false;
  if (a == "natRange")
    return !decimalLess(text(right, "maximum"), text(left, "minimum")) &&
           !decimalLess(text(left, "maximum"), text(right, "minimum"));
  if (a == "domain")
    return text(left, "sort") == text(right, "sort") &&
           text(left, "identity") == text(right, "identity");
  // Exact type patterns overlap when their trees are structurally equal.
  std::function<bool(const Record *, const Record *)> equalTree =
      [&](const Record *x, const Record *y) {
        auto xs = x->getValueAsListOfDefs("arguments");
        auto ys = y->getValueAsListOfDefs("arguments");
        if (text(x, "constructor") != text(y, "constructor") ||
            xs.size() != ys.size())
          return false;
        for (auto [p, q] : zip(xs, ys)) {
          if (text(p, "kind") != text(q, "kind"))
            return false;
          auto kind = text(p, "kind");
          if (kind == "domain" ? text(p, "sort") != text(q, "sort") ||
                                     text(p, "identity") != text(q, "identity")
              : kind == "nat"  ? text(p, "value") != text(q, "value")
                               : !equalTree(p->getValueAsDef("type"),
                                            q->getValueAsDef("type")))
            return false;
        }
        return true;
      };
  return equalTree(left->getValueAsDef("type"), right->getValueAsDef("type"));
}

void Physical::checkApplied() {
  for (const auto *row : applied) {
    exactFields(row, {"constructor", "arguments", "identity", "isDefault",
                      "child", "frame", "provider", "unit", "vectorPort"});
    auto constructor = text(row, "constructor");
    require(catalogName(text(row, "identity")), row,
            "invalid representation identity");
    const Record *declared = nullptr;
    Records ps;
    if (constructor != "variant") {
      declared = logical.type(constructor);
      require(declared, row, "undeclared constructor " + constructor);
      ps = declared->getValueAsListOfDefs("parameters");
      require(!ps.empty(), row,
              "applied representation needs a parameterized constructor");
    }
    auto patterns = row->getValueAsListOfDefs("arguments");
    require(patterns.size() == ps.size(), row,
            "applied representation pattern count differs");
    for (auto [pattern, p] : zip(patterns, ps)) {
      auto kind = text(pattern, "kind");
      auto [parameterKind, parameterSort] = parameter(p);
      if (kind == "any") {
        exactFields(pattern, {"kind"});
      } else if (kind == "domain") {
        exactFields(pattern, {"kind", "sort", "identity"});
        require(parameterKind == "Domain" &&
                    text(pattern, "sort") == parameterSort &&
                    logical.resolves(parameterSort, text(pattern, "identity")),
                row, "domain argument disagrees with its parameter");
      } else if (kind == "type") {
        exactFields(pattern, {"kind", "type"});
        require(parameterKind == "Type", row,
                "type argument disagrees with its parameter");
        typeTree(row, pattern->getValueAsDef("type"));
      } else if (kind == "natRange") {
        exactFields(pattern, {"kind", "minimum", "maximum"});
        auto minimum = text(pattern, "minimum"),
             maximum = text(pattern, "maximum");
        require(parameterKind == "Nat" && canonicalDecimal(minimum) &&
                    canonicalDecimal(maximum) &&
                    !decimalLess(maximum, minimum) &&
                    !decimalLess(std::to_string(staticNaturalLimit), maximum),
                row, "invalid natural range");
      } else
        PrintFatalError(row, "unknown argument pattern");
    }
    if (const auto *child = nullableDef(row, "child")) {
      exactFields(child, {"kind", "domain", "representation"});
      // The single dense child is the collection element of the first
      // parameter, so the first pattern must determine it.
      const auto *collection =
          declared ? nullableDef(declared, "collection") : nullptr;
      require(collection && text(collection, "element") == "parameter" &&
                  !patterns.empty() && text(patterns[0], "kind") != "any",
              row, "a child representation needs a determined dense element");
      std::pair<std::string, std::string> element;
      if (text(patterns[0], "kind") == "domain") {
        auto sort = text(patterns[0], "sort");
        element = {sort == "Field"   ? "field"
                   : sort == "Group" ? "group"
                                     : "",
                   text(patterns[0], "identity").str()};
      } else {
        const auto *tree = patterns[0]->getValueAsDef("type");
        auto arguments = tree->getValueAsListOfDefs("arguments");
        require(arguments.empty() || (arguments.size() == 1 &&
                                      text(arguments[0], "kind") == "domain"),
                row, "a dense element is an atomic instance");
        element = {text(tree, "constructor").str(),
                   arguments.empty() ? std::string()
                                     : text(arguments[0], "identity").str()};
      }
      require(element == std::make_pair(text(child, "kind").str(),
                                        text(child, "domain").str()),
              row, "child is not the logical element");
      require(
          keys.count({text(child, "kind").str(), text(child, "domain").str(),
                      text(child, "representation").str()}),
          row, "child names no representation row");
    }
    // The dense calling convention: the provider whose dense operations use
    // this container, and the vector representation they exchange.
    const auto *child = nullableDef(row, "child");
    const auto *port = nullableDef(row, "vectorPort");
    require(row->isValueUnset("provider") == !child && !port == !child, row,
            "a provider and a vector port are declared exactly for a dense "
            "child");
    if (child) {
      exactFields(port, {"kind", "domain", "representation"});
      require(text(port, "kind") == "vector" &&
                  text(port, "domain") == text(child, "domain"),
              row, "vector port is not a vector over the child's domain");
      auto found =
          keys.find({text(port, "kind").str(), text(port, "domain").str(),
                     text(port, "representation").str()});
      require(found != keys.end(), row,
              "vector port names no representation row");
      require(text(found->second, "layout").empty(), row,
              "vector port names a layout selection");
      require(text(found->second, "unit") == text(row, "unit"), row,
              "vector port storage belongs to another unit");
      auto provider = text(row, "provider");
      auto unit = units.find(provider.str());
      require(is_contained(providerNames, provider) && unit != units.end() &&
                  unit->second == text(row, "unit"),
              row, "dense provider is installed by another unit");
      auto preference = providerRows.find(text(child, "domain").str());
      require(preference != providerRows.end() &&
                  (text(preference->second, "provider") == provider ||
                   is_contained(preference->second->getValueAsListOfStrings(
                                    "alternatives"),
                                provider)),
              row, "dense provider is not a provider of the child's domain");
    }
    require(text(row, "frame") == "canonical" || text(row, "frame") == "local",
            row, "unknown representation frame");
    require(is_contained(unitNames, text(row, "unit")), row,
            "unknown installation unit");
    // A canonical applied row needs its constructor's aggregate frame; a
    // field_array frame is granted per field, so the row names it exactly.
    if (text(row, "frame") == "canonical") {
      std::string field;
      if (constructor == "field_array" && !patterns.empty() &&
          text(patterns[0], "kind") == "domain")
        field = text(patterns[0], "identity").str();
      require((constructor == "field_array") == !field.empty() &&
                  logical.aggregates.count({constructor.str(), field}),
              row,
              "a canonical applied representation requires its aggregate "
              "frame");
    }
  }
  for (auto [index, row] : enumerate(applied))
    for (const auto *other : ArrayRef(applied).take_front(index)) {
      if (text(other, "constructor") != text(row, "constructor"))
        continue;
      auto left = row->getValueAsListOfDefs("arguments");
      auto right = other->getValueAsListOfDefs("arguments");
      if (!all_of(zip(left, right), [](const auto &pair) {
            return overlaps(std::get<0>(pair), std::get<1>(pair));
          }))
        continue;
      require(text(row, "identity") != text(other, "identity"), row,
              "overlapping applied representations share an identity");
      require(!(row->getValueAsBit("isDefault") &&
                other->getValueAsBit("isDefault")),
              row, "overlapping applied representations are both defaults");
    }
  // One calling convention per provider and dense constructor.
  std::set<std::pair<std::string, std::string>> conventions;
  for (const auto *row : applied)
    if (nullableDef(row, "child"))
      require(conventions
                  .emplace(text(row, "constructor").str(),
                           text(row, "provider").str())
                  .second,
              row, "second dense container of one provider");
}

void Physical::checkFieldForms() {
  std::set<std::string> fields;
  for (const auto *row : fieldForms) {
    exactFields(row,
                {"fieldDomain", "arithmetic", "montgomery", "byteEncoding"});
    auto field = text(row, "fieldDomain");
    const auto *domain = logical.fieldRow(field, row);
    require(fields.insert(field.str()).second, row, "duplicate field form");
    const auto *arithmetic = nullableDef(row, "arithmetic");
    if (arithmetic) {
      exactFields(arithmetic, {"form", "representation"});
      auto found = defaults.find({"field", field.str()});
      require(
          text(arithmetic, "form") == "residue" && found != defaults.end() &&
              text(found->second, "identity") ==
                  text(arithmetic, "representation"),
          row, "residue arithmetic names the field's default representation");
      // Residue arithmetic is installed on a prime field or on a binomial
      // extension B[X]/(X^degree - c) of a prime base; its coordinates take
      // the prime base's framed field codec.
      const auto *shape = logical.structure(domain);
      const Record *base = domain;
      if (text(shape, "kind") != "prime") {
        auto member = logical.member(domain, "BaseField");
        auto reduction = shape->getValueAsListOfDefs("reduction");
        base = text(shape, "over") == "BaseField" && member
                   ? logical.fieldRow(*member, row)
                   : nullptr;
        require(base && reduction.size() == 1 &&
                    reduction.front()->getValueAsInt("exponent") == 0 &&
                    text(logical.structure(base), "kind") == "prime",
                row,
                "residue arithmetic requires a prime field or a binomial "
                "extension of a prime base");
      }
      require(framed("field", text(base, "identity")), row,
              "residue arithmetic requires a framed field codec of its prime "
              "base");
    }
    if (const auto *montgomery = nullableDef(row, "montgomery")) {
      exactFields(montgomery, {"wordBytes", "radixBits"});
      const auto word = montgomery->getValueAsInt("wordBytes");
      const auto radix = montgomery->getValueAsInt("radixBits");
      require(arithmetic, row, "Montgomery words require residue arithmetic");
      require(word >= 1 && radix <= staticNaturalLimit && word * 8 == radix,
              row, "Montgomery radix is the word width");
      require(decimalBits(text(logical.facts(domain), "characteristic")) <=
                  uint64_t(radix),
              row, "characteristic exceeds the Montgomery radix");
    }
    if (const auto *encoding = nullableDef(row, "byteEncoding")) {
      exactFields(encoding, {"codec", "order"});
      auto found = logical.codecRows.find(text(encoding, "codec").str());
      require(found != logical.codecRows.end() &&
                  text(found->second, "kind") == "field" &&
                  text(found->second, "domain") == field &&
                  nullableDef(found->second, "frame") &&
                  text(encoding, "order") == "littleEndian",
              row, "byte encoding names the field's framed field codec");
    }
  }
}

std::string quote(StringRef s) {
  std::string result;
  raw_string_ostream os(result);
  os << '"';
  os.write_escaped(s);
  os << '"';
  return result;
}
std::string strings(ArrayRef<StringRef> values) {
  std::string result = "{";
  for (auto [i, value] : enumerate(values))
    result += (i ? ", " : "") + quote(value);
  return result + "}";
}
std::string optionalNumber(const Record *r, StringRef field) {
  return r->isValueUnset(field) ? "std::nullopt"
                                : std::to_string(r->getValueAsInt(field));
}
std::string scheme(StringRef value) {
  return "CommitmentScheme::" +
         std::string(value == "keccak256Rows"   ? "Keccak256Rows"
                     : value == "poseidon2Rows" ? "Poseidon2Rows"
                                                : "MultilinearKzg");
}
std::string capitalized(StringRef value) {
  std::string result = value.str();
  result.front() = toUpper(result.front());
  return result;
}

void emitDomains(raw_ostream &os, const Logical &m) {
  os << "llvm::ArrayRef<Domain> domains() {\n"
        "static const std::vector<Domain> rows = {\n";
  for (const auto *row : m.domains) {
    os << "{" << quote(text(row, "identity")) << ", "
       << quote(text(row, "sort")) << ", {";
    for (auto [member, identity] : memberPairs(row))
      os << "{" << quote(member) << ", " << quote(identity) << "}, ";
    os << "}, " << strings(row->getValueAsListOfStrings("capabilities"))
       << ", ";
    if (const auto *facts = nullableDef(row, "fieldFacts")) {
      const auto *shape = facts->getValueAsDef("structure");
      os << "FieldFacts{" << quote(text(facts, "characteristic")) << ", ";
      if (text(shape, "kind") == "prime")
        os << "std::nullopt";
      else {
        os << "FieldExtension{ExtensionBase::" << text(shape, "over") << ", "
           << shape->getValueAsInt("degree") << ", {";
        for (const auto *term : shape->getValueAsListOfDefs("reduction"))
          os << "{" << term->getValueAsInt("exponent") << ", "
             << quote(text(term, "coefficient")) << "}, ";
        os << "}}";
      }
      os << ", ";
      if (const auto *twoAdic = nullableDef(facts, "twoAdic"))
        os << "TwoAdicConvention{" << quote(text(twoAdic, "convention")) << ", "
           << quote(text(twoAdic, "maximalRoot")) << ", "
           << twoAdic->getValueAsInt("twoAdicity") << ", "
           << quote(text(twoAdic, "ordering")) << "}";
      else
        os << "std::nullopt";
      os << "}";
    } else
      os << "std::nullopt";
    os << ", ";
    if (const auto *facts = nullableDef(row, "transcriptFacts"))
      os << "TranscriptFacts{" << quote(text(facts, "family")) << ", "
         << (facts->isValueUnset("hash")
                 ? std::string("std::nullopt")
                 : "std::string(" + quote(text(facts, "hash")) + ")")
         << ", " << quote(text(facts, "decoder")) << ", "
         << (facts->getValueAsBit("bindsSuite") ? "true" : "false") << "}";
    else
      os << "std::nullopt";
    os << ", ";
    if (const auto *facts = nullableDef(row, "commitmentFacts"))
      os << "CommitmentFacts{" << scheme(text(facts, "scheme")) << ", "
         << optionalNumber(facts, "digestBytes") << ", "
         << (facts->isValueUnset("permutation")
                 ? std::string("std::nullopt")
                 : "std::string(" + quote(text(facts, "permutation")) + ")")
         << ", " << optionalNumber(facts, "digestWordBytes") << "}";
    else
      os << "std::nullopt";
    os << "},\n";
  }
  os << "}; return rows; }\n";
}

void emitLogicalTables(raw_ostream &os, const Logical &m) {
  os << "namespace instances {\n";
  emitDomains(os, m);
  os << "llvm::ArrayRef<LogicalType> logicalTypes() {\n"
        "static const std::vector<LogicalType> rows = {\n";
  for (const auto *row : m.logicalTypes)
    os << "{" << quote(text(row, "kind")) << ", " << quote(text(row, "domain"))
       << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<FrameTag> frameTags() {\n"
        "static const std::vector<FrameTag> rows = {\n";
  for (const auto *row : m.frameTags) {
    os << "{" << row->getValueAsInt("tag")
       << ", FrameLayout::" << text(row, "layout") << ", ";
    if (const auto *shared = nullableDef(row, "shared"))
      os << "SharedFrame{" << quote(text(shared, "kind")) << ", "
         << scheme(text(shared, "scheme")) << "}";
    else
      os << "std::nullopt";
    os << "},\n";
  }
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<Codec> codecs() {\n"
        "static const std::vector<Codec> rows = {\n";
  for (const auto *row : m.codecs) {
    os << "{" << quote(text(row, "identity")) << ", "
       << quote(text(row, "kind")) << ", " << quote(text(row, "domain"))
       << ", ";
    if (const auto *frame = nullableDef(row, "frame"))
      os << "CodecFrame{" << frame->getValueAsInt("tag") << ", "
         << optionalNumber(frame, "elementBytes") << ", "
         << optionalNumber(frame, "bytes") << ", "
         << optionalNumber(frame, "bytesPerArity") << "}";
    else
      os << "std::nullopt";
    os << "},\n";
  }
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<AggregateFrame> aggregateFrames() {\n"
        "static const std::vector<AggregateFrame> rows = {\n";
  for (const auto *row : m.aggregateFrames)
    os << "{" << quote(text(row, "constructor")) << ", "
       << quote(text(row, "domain")) << ", " << row->getValueAsInt("tag")
       << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<RandomService> randomServices() {\n"
        "static const std::vector<RandomService> rows = {\n";
  for (const auto *row : m.services)
    os << "{" << quote(text(row, "contract")) << ", "
       << quote(text(row, "fieldDomain")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<Limit> limits() {\n"
        "static const std::vector<Limit> rows = {\n";
  for (const auto *row : m.limits)
    os << "{" << quote(text(row, "name")) << ", " << row->getValueAsInt("value")
       << "u, LimitUnit::" << capitalized(text(row, "unit")) << ", "
       << quote(text(row, "owner")) << ", " << quote(text(row, "scope"))
       << ", LimitPhase::" << capitalized(text(row, "phase")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<FiniteDefinition> finiteDefinitions() {\n"
        "static const std::vector<FiniteDefinition> rows = {\n";
  for (const auto *row : m.finiteDefinitions)
    os << "{" << quote(text(row, "identity"))
       << ", FiniteMode::" << capitalized(text(row, "mode"))
       << ", FiniteOperation::" << capitalized(text(row, "operation")) << ", "
       << (row->isValueUnset("collection")
               ? std::string("std::nullopt")
               : "std::string(" + quote(text(row, "collection")) + ")")
       << ", " << (row->getValueAsBit("filtered") ? "true" : "false") << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<DomainConstructor> domainConstructors() {\n"
        "static const std::vector<DomainConstructor> rows = {\n";
  for (const auto *row : m.domainConstructors)
    os << "{" << quote(text(row, "identity"))
       << ", DomainConstructorKind::" << text(row, "kind") << ", "
       << row->getValueAsInt("axis") << "},\n";
  os << "}; return rows; }\n";
  os << "} // namespace instances\n";
}

std::string typeTreeValue(const Record *tree) {
  std::string result = "TypeTree{" + quote(text(tree, "constructor")) + ", {";
  for (const auto *argument : tree->getValueAsListOfDefs("arguments")) {
    auto kind = text(argument, "kind");
    if (kind == "domain")
      result += "TypeTreeArgument{TypeTreeArgument::Kind::Domain, " +
                quote(text(argument, "sort")) + ", " +
                quote(text(argument, "identity")) + ", std::nullopt, {}}, ";
    else if (kind == "type")
      result += "TypeTreeArgument{TypeTreeArgument::Kind::Type, {}, {}, " +
                typeTreeValue(argument->getValueAsDef("type")) + ", {}}, ";
    else
      result += "TypeTreeArgument{TypeTreeArgument::Kind::Nat, {}, {}, "
                "std::nullopt, " +
                quote(text(argument, "value")) + "}, ";
  }
  return result + "}}";
}

void emitPhysicalTables(raw_ostream &os, const Physical &m) {
  auto frame = [](const Record *row) {
    return text(row, "frame") == "canonical" ? "ValueFrame::Canonical"
                                             : "ValueFrame::Local";
  };
  os << "namespace installation {\n";
  os << "llvm::ArrayRef<Representation> representations() {\n"
        "static const std::vector<Representation> rows = {\n";
  for (const auto *row : m.representations)
    os << "{" << quote(text(row, "identity")) << ", "
       << quote(text(row, "kind")) << ", " << quote(text(row, "domain")) << ", "
       << (row->getValueAsBit("isDefault") ? "true" : "false") << ", "
       << quote(text(row, "layout")) << ", " << frame(row) << ", "
       << quote(text(row, "unit")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<AppliedRepresentation> appliedRepresentations() {\n"
        "static const std::vector<AppliedRepresentation> rows = {\n";
  for (const auto *row : m.applied) {
    os << "{" << quote(text(row, "constructor")) << ", {";
    for (const auto *pattern : row->getValueAsListOfDefs("arguments")) {
      auto kind = text(pattern, "kind");
      if (kind == "any")
        os << "ArgumentPattern{ArgumentPattern::Kind::Any, {}, {}, "
              "std::nullopt, 0, 0}, ";
      else if (kind == "domain")
        os << "ArgumentPattern{ArgumentPattern::Kind::Domain, "
           << quote(text(pattern, "sort")) << ", "
           << quote(text(pattern, "identity")) << ", std::nullopt, 0, 0}, ";
      else if (kind == "type")
        os << "ArgumentPattern{ArgumentPattern::Kind::Type, {}, {}, "
           << typeTreeValue(pattern->getValueAsDef("type")) << ", 0, 0}, ";
      else
        os << "ArgumentPattern{ArgumentPattern::Kind::NatRange, {}, {}, "
              "std::nullopt, "
           << text(pattern, "minimum") << "u, " << text(pattern, "maximum")
           << "u}, ";
    }
    auto reference = [&](StringRef field) {
      if (const auto *value = nullableDef(row, field))
        os << "RepresentationReference{" << quote(text(value, "kind")) << ", "
           << quote(text(value, "domain")) << ", "
           << quote(text(value, "representation")) << "}";
      else
        os << "std::nullopt";
    };
    os << "}, " << quote(text(row, "identity")) << ", "
       << (row->getValueAsBit("isDefault") ? "true" : "false") << ", ";
    reference("child");
    os << ", " << frame(row) << ", "
       << (row->isValueUnset("provider")
               ? std::string("std::nullopt")
               : "std::string(" + quote(text(row, "provider")) + ")")
       << ", " << quote(text(row, "unit")) << ", ";
    reference("vectorPort");
    os << "},\n";
  }
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<Provider> providers() {\n"
        "static const std::vector<Provider> rows = {\n";
  for (const auto *row : m.providers)
    os << "{" << quote(text(row, "domain")) << ", "
       << quote(text(row, "provider")) << ", "
       << strings(row->getValueAsListOfStrings("alternatives")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<ProviderUnit> providerUnits() {\n"
        "static const std::vector<ProviderUnit> rows = {\n";
  for (const auto *row : m.providerUnits)
    os << "{" << quote(text(row, "provider")) << ", "
       << quote(text(row, "unit")) << "},\n";
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<FieldForm> fieldForms() {\n"
        "static const std::vector<FieldForm> rows = {\n";
  for (const auto *row : m.fieldForms) {
    os << "{" << quote(text(row, "fieldDomain")) << ", ";
    if (const auto *arithmetic = nullableDef(row, "arithmetic"))
      os << "ResidueArithmetic{" << quote(text(arithmetic, "form")) << ", "
         << quote(text(arithmetic, "representation")) << "}";
    else
      os << "std::nullopt";
    os << ", ";
    if (const auto *montgomery = nullableDef(row, "montgomery"))
      os << "MontgomeryForm{" << montgomery->getValueAsInt("wordBytes") << ", "
         << montgomery->getValueAsInt("radixBits") << "}";
    else
      os << "std::nullopt";
    os << ", ";
    if (const auto *encoding = nullableDef(row, "byteEncoding"))
      os << "ByteEncoding{" << quote(text(encoding, "codec")) << ", "
         << quote(text(encoding, "order")) << "}";
    else
      os << "std::nullopt";
    os << "},\n";
  }
  os << "}; return rows; }\n";
  os << "llvm::ArrayRef<PhysicalArguments> physicalArguments() {\n"
        "static const std::vector<PhysicalArguments> rows = {\n";
  for (const auto *row : m.physicalArguments)
    os << "{" << quote(text(row, "operation")) << "},\n";
  os << "}; return rows; }\n";
  os << "} // namespace installation\n";
}

json::Value nullableString(const Record *r, StringRef field) {
  return r->isValueUnset(field) ? json::Value(nullptr)
                                : json::Value(text(r, field));
}
json::Array stringsJSON(ArrayRef<StringRef> values) {
  json::Array result;
  for (auto value : values)
    result.push_back(value);
  return result;
}

json::Object domainJSON(const Record *row) {
  json::Array members;
  for (auto [member, identity] : memberPairs(row))
    members.push_back(json::Array{member, identity});
  json::Object result{{"identity", text(row, "identity")},
                      {"sort", text(row, "sort")},
                      {"members", std::move(members)},
                      {"capabilities", stringsJSON(row->getValueAsListOfStrings(
                                           "capabilities"))}};
  if (const auto *facts = nullableDef(row, "fieldFacts")) {
    const auto *shape = facts->getValueAsDef("structure");
    json::Object structure{{"kind", text(shape, "kind")}};
    if (text(shape, "kind") == "extension") {
      json::Array reduction;
      for (const auto *term : shape->getValueAsListOfDefs("reduction"))
        reduction.push_back(json::Array{term->getValueAsInt("exponent"),
                                        text(term, "coefficient")});
      structure["over"] = text(shape, "over");
      structure["degree"] = shape->getValueAsInt("degree");
      structure["reduction"] = std::move(reduction);
    }
    json::Value twoAdic = nullptr;
    if (const auto *convention = nullableDef(facts, "twoAdic"))
      twoAdic =
          json::Object{{"convention", text(convention, "convention")},
                       {"maximalRoot", text(convention, "maximalRoot")},
                       {"twoAdicity", convention->getValueAsInt("twoAdicity")},
                       {"ordering", text(convention, "ordering")}};
    result["field"] =
        json::Object{{"characteristic", text(facts, "characteristic")},
                     {"structure", std::move(structure)},
                     {"twoAdic", std::move(twoAdic)}};
  }
  if (const auto *facts = nullableDef(row, "transcriptFacts"))
    result["transcript"] =
        json::Object{{"family", text(facts, "family")},
                     {"hash", nullableString(facts, "hash")},
                     {"decoder", text(facts, "decoder")},
                     {"bindsSuite", facts->getValueAsBit("bindsSuite")}};
  if (const auto *facts = nullableDef(row, "commitmentFacts")) {
    json::Object commitment{{"scheme", text(facts, "scheme")}};
    for (auto field : {"digestBytes", "digestWordBytes"})
      if (!facts->isValueUnset(field))
        commitment[field] = facts->getValueAsInt(field);
    if (!facts->isValueUnset("permutation"))
      commitment["permutation"] = text(facts, "permutation");
    result["commitment"] = std::move(commitment);
  }
  return result;
}

json::Value patternJSON(const Record *pattern);
json::Array typeTreeJSON(const Record *tree) {
  json::Array arguments;
  for (const auto *argument : tree->getValueAsListOfDefs("arguments")) {
    auto kind = text(argument, "kind");
    if (kind == "domain")
      arguments.push_back(json::Array{"domain", text(argument, "sort"),
                                      text(argument, "identity")});
    else if (kind == "type")
      arguments.push_back(
          json::Array{"type", typeTreeJSON(argument->getValueAsDef("type"))});
    else
      arguments.push_back(json::Array{"nat", text(argument, "value")});
  }
  return json::Array{"apply", text(tree, "constructor"), std::move(arguments)};
}
json::Value patternJSON(const Record *pattern) {
  auto kind = text(pattern, "kind");
  if (kind == "any")
    return json::Array{"any"};
  if (kind == "domain")
    return json::Array{"domain", text(pattern, "sort"),
                       text(pattern, "identity")};
  if (kind == "type")
    return json::Array{"type", typeTreeJSON(pattern->getValueAsDef("type"))};
  return json::Array{"natRange", text(pattern, "minimum"),
                     text(pattern, "maximum")};
}

json::Object installationJSON(const Physical &m) {
  json::Array representations, applied, providers, units, forms, arguments;
  for (const auto *row : m.representations)
    representations.push_back(
        json::Object{{"identity", text(row, "identity")},
                     {"kind", text(row, "kind")},
                     {"domain", text(row, "domain")},
                     {"default", row->getValueAsBit("isDefault")},
                     {"layout", text(row, "layout")},
                     {"frame", text(row, "frame")},
                     {"unit", text(row, "unit")}});
  for (const auto *row : m.applied) {
    json::Array patterns;
    for (const auto *pattern : row->getValueAsListOfDefs("arguments"))
      patterns.push_back(patternJSON(pattern));
    auto reference = [&](StringRef field) -> json::Value {
      if (const auto *c = nullableDef(row, field))
        return json::Object{{"kind", text(c, "kind")},
                            {"domain", text(c, "domain")},
                            {"representation", text(c, "representation")}};
      return nullptr;
    };
    json::Value provider = nullptr;
    if (!row->isValueUnset("provider"))
      provider = text(row, "provider");
    applied.push_back(json::Object{{"constructor", text(row, "constructor")},
                                   {"arguments", std::move(patterns)},
                                   {"identity", text(row, "identity")},
                                   {"default", row->getValueAsBit("isDefault")},
                                   {"child", reference("child")},
                                   {"frame", text(row, "frame")},
                                   {"provider", std::move(provider)},
                                   {"unit", text(row, "unit")},
                                   {"vectorPort", reference("vectorPort")}});
  }
  for (const auto *row : m.providers)
    providers.push_back(json::Object{
        {"domain", text(row, "domain")},
        {"default", text(row, "provider")},
        {"alternatives",
         stringsJSON(row->getValueAsListOfStrings("alternatives"))}});
  for (const auto *row : m.providerUnits)
    units.push_back(json::Object{{"provider", text(row, "provider")},
                                 {"unit", text(row, "unit")}});
  for (const auto *row : m.fieldForms) {
    json::Value arithmetic = nullptr, montgomery = nullptr, encoding = nullptr;
    if (const auto *a = nullableDef(row, "arithmetic"))
      arithmetic = json::Object{{"form", text(a, "form")},
                                {"representation", text(a, "representation")}};
    if (const auto *w = nullableDef(row, "montgomery"))
      montgomery = json::Object{{"wordBytes", w->getValueAsInt("wordBytes")},
                                {"radixBits", w->getValueAsInt("radixBits")}};
    if (const auto *b = nullableDef(row, "byteEncoding"))
      encoding = json::Object{{"codec", text(b, "codec")},
                              {"order", text(b, "order")}};
    forms.push_back(json::Object{{"field", text(row, "fieldDomain")},
                                 {"arithmetic", std::move(arithmetic)},
                                 {"montgomery", std::move(montgomery)},
                                 {"byteEncoding", std::move(encoding)}});
  }
  for (const auto *row : m.physicalArguments)
    arguments.push_back(json::Object{{"operation", text(row, "operation")}});
  return json::Object{{"format", "zkc.native-installation/0"},
                      {"representations", std::move(representations)},
                      {"appliedRepresentations", std::move(applied)},
                      {"providers", std::move(providers)},
                      {"providerUnits", std::move(units)},
                      {"fieldForms", std::move(forms)},
                      {"physicalArguments", std::move(arguments)}};
}
} // namespace

void validateInstalledInstances(const RecordKeeper &records) {
  Logical validated(records);
}

void addInstalledInstanceInventory(json::Object &result,
                                   const RecordKeeper &records) {
  Logical m(records);
  json::Array domains, types, tags, codecs, aggregates, services, limits,
      finite, constructors;
  for (const auto *row : m.domains)
    domains.push_back(domainJSON(row));
  for (const auto *row : m.logicalTypes)
    types.push_back(json::Object{{"kind", text(row, "kind")},
                                 {"domain", text(row, "domain")}});
  for (const auto *row : m.frameTags) {
    json::Value shared = nullptr;
    if (const auto *s = nullableDef(row, "shared"))
      shared = json::Object{{"kind", text(s, "kind")},
                            {"scheme", text(s, "scheme")}};
    tags.push_back(json::Object{{"tag", row->getValueAsInt("tag")},
                                {"layout", text(row, "layout")},
                                {"shared", std::move(shared)}});
  }
  for (const auto *row : m.codecs) {
    json::Value frame = nullptr;
    if (const auto *f = nullableDef(row, "frame")) {
      json::Object object{{"tag", f->getValueAsInt("tag")}};
      for (auto field : {"elementBytes", "bytes", "bytesPerArity"})
        if (!f->isValueUnset(field))
          object[field] = f->getValueAsInt(field);
      frame = std::move(object);
    }
    codecs.push_back(json::Object{{"identity", text(row, "identity")},
                                  {"kind", text(row, "kind")},
                                  {"domain", text(row, "domain")},
                                  {"frame", std::move(frame)}});
  }
  for (const auto *row : m.aggregateFrames)
    aggregates.push_back(json::Object{{"constructor", text(row, "constructor")},
                                      {"domain", text(row, "domain")},
                                      {"tag", row->getValueAsInt("tag")}});
  for (const auto *row : m.services)
    services.push_back(json::Object{{"contract", text(row, "contract")},
                                    {"field", text(row, "fieldDomain")}});
  for (const auto *row : m.limits)
    limits.push_back(json::Object{{"name", text(row, "name")},
                                  {"value", row->getValueAsInt("value")},
                                  {"unit", text(row, "unit")},
                                  {"owner", text(row, "owner")},
                                  {"scope", text(row, "scope")},
                                  {"phase", text(row, "phase")}});
  for (const auto *row : m.finiteDefinitions)
    finite.push_back(
        json::Object{{"identity", text(row, "identity")},
                     {"mode", text(row, "mode")},
                     {"operation", text(row, "operation")},
                     {"collection", nullableString(row, "collection")},
                     {"filtered", row->getValueAsBit("filtered")}});
  for (const auto *row : m.domainConstructors)
    constructors.push_back(json::Object{{"identity", text(row, "identity")},
                                        {"kind", text(row, "kind")},
                                        {"axis", row->getValueAsInt("axis")}});
  result["domains"] = std::move(domains);
  result["logicalTypes"] = std::move(types);
  result["frameTags"] = std::move(tags);
  result["codecs"] = std::move(codecs);
  result["aggregateFrames"] = std::move(aggregates);
  result["randomServices"] = std::move(services);
  result["limits"] = std::move(limits);
  result["finiteDefinitions"] = std::move(finite);
  result["domainConstructors"] = std::move(constructors);
}

bool emitInstalledInstances(raw_ostream &os, const RecordKeeper &records) {
  Logical logical(records);
  Physical physical(records, logical);
  os << "// Generated from the installed-instance declarations and their "
        "native\n// installation. Do not edit.\n";
  os << "#ifdef ZKC_INSTALLED_LIMIT_VALUES\n#undef ZKC_INSTALLED_LIMIT_VALUES\n"
     << "inline constexpr std::array<LimitValue, " << logical.limits.size()
     << "> limitValues = {{\n";
  for (const auto *row : logical.limits)
    os << "{" << quote(text(row, "name")) << ", " << row->getValueAsInt("value")
       << "u},\n";
  os << "}};\n#endif\n";
  os << "#ifdef ZKC_INSTALLED_INSTANCE_TABLES\n"
        "#undef ZKC_INSTALLED_INSTANCE_TABLES\n";
  emitLogicalTables(os, logical);
  emitPhysicalTables(os, physical);
  os << "#endif\n";
  return false;
}

bool emitNativeInstallationInventory(raw_ostream &os,
                                     const RecordKeeper &records) {
  Logical logical(records);
  Physical physical(records, logical);
  os << formatv("{0:2}\n", json::Value(installationJSON(physical)));
  return false;
}
