#include "LanguageInterface.h"
#include "mlir/IR/Builders.h"
#include "zkc/Compiler/Host.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/Relation.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Names.h"
#include "zkc/Language/RelationABI.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/FramedHash.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Entry.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <iterator>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::language::detail {
namespace {
bool hash(StringRef value) {
  return value.size() == 64 && all_of(value, [](char c) {
           return isDigit(c) || (c >= 'a' && c <= 'f');
         });
}
class Reader {
  const Limits &limits;
  uint64_t remaining;
  protocol::TypeParseBudget typeBudget;
  Error failure = Error::success();
  LanguageInterface view;
  InterfaceProtocol *current = nullptr;
  ArrayRef<Asset> assets;
  StringMap<unsigned> relationIndices;
  std::map<std::tuple<std::string, std::string, std::string, std::string>,
           unsigned>
      relationIdentities;
  std::map<std::string, protocol_ir::MathematicalOp> nativeProtocols;
  std::map<std::string, relation::DeclareOp> nativeRelations;
  std::map<std::string, protocol_ir::ConstructionOp> nativeConstructions;
  std::map<std::string, mlir::func::FuncOp> helpers;
  relation::FormulaIdentities formulas;
  std::map<const InterfaceSchema *, std::string> schemaIdentities;
  std::map<std::string, std::shared_ptr<const InterfaceSchema>> schemas;
  StringMap<unsigned> roleIndices;
  struct NativeLeaf {
    Permissions permissions;
    bool participants, constructible, total;
    bool setup = false, verifierKey = false, proverKey = false;
  };
  std::map<std::string, NativeLeaf> nativeLeaves;
  bool fail(StringRef message) {
    if (!failure)
      failure = error("source.interface", message);
    return false;
  }
  bool charge(uint64_t amount) {
    if (failure)
      return false;
    if (amount > remaining) {
      failure = error("source.limit", "interface reader work limit exceeded");
      return false;
    }
    remaining -= amount;
    return true;
  }
  const json::Object *object(const json::Value &value,
                             std::initializer_list<StringRef> keys) {
    auto *result = value.getAsObject();
    if (!result || result->size() != keys.size() ||
        !all_of(keys, [&](auto key) { return result->get(key); })) {
      fail("interface object members differ");
      return nullptr;
    }
    return result;
  }
  const json::Array *array(const json::Object &value, StringRef name) {
    auto *result = value.getArray(name);
    if (!result)
      fail("expected interface array");
    return result;
  }
  std::optional<StringRef>
  text(const json::Object &value, StringRef name,
       uint64_t ceiling = protocol::VariantSpellingBytes) {
    auto result = value.getString(name);
    if (!result || result->empty()) {
      fail("invalid interface string");
      return {};
    }
    if (result->size() > ceiling) {
      if (!failure)
        failure = error("source.limit", "interface string limit exceeded");
      return {};
    }
    if (!charge(1 + result->size()))
      return {};
    return result;
  }
  std::optional<unsigned> natural(const json::Object &value, StringRef name) {
    auto result = value.getInteger(name);
    if (!result || *result < 0 || uint64_t(*result) > UINT32_MAX) {
      fail("expected bounded interface index");
      return {};
    }
    return unsigned(*result);
  }
  std::optional<std::vector<unsigned>> roles(const json::Array &array) {
    if (!charge(array.size() + 1))
      return {};
    std::vector<unsigned> result;
    for (const auto &item : array) {
      auto name = item.getAsString();
      if (!name) {
        fail("invalid role name");
        return {};
      }
      auto found = roleIndices.find(*name);
      if (found == roleIndices.end() ||
          (!result.empty() && found->second <= result.back())) {
        fail("unknown, repeated or unordered role");
        return {};
      }
      result.push_back(found->second);
    }
    if (result.empty()) {
      fail("empty port roles");
      return {};
    }
    return result;
  }
  bool matchesRoles(mlir::Attribute attribute, ArrayRef<unsigned> roles) {
    auto array = mlir::dyn_cast_if_present<mlir::ArrayAttr>(attribute);
    if (!array || array.size() != roles.size())
      return fail("native role arity differs");
    for (unsigned i = 0; i < roles.size(); ++i) {
      auto name = mlir::dyn_cast<mlir::StringAttr>(array[i]);
      if (!name || name.getValue() != nativeRoleName(roles[i]))
        return fail("native participant mapping differs");
    }
    return true;
  }
  std::optional<Permissions> permissions(const json::Array &values) {
    Permissions result;
    const StringRef order[] = {"Copy", "Drop"};
    unsigned next = 0;
    for (const auto &item : values) {
      auto value = item.getAsString();
      if (!value) {
        fail("invalid or repeated permission");
        return {};
      }
      auto found = llvm::find(ArrayRef(order).drop_front(next), *value);
      if (found == std::end(order)) {
        fail("unknown, repeated or unordered permission");
        return {};
      }
      next = found - std::begin(order) + 1;
      if (*value == "Copy")
        result.copy = true;
      else if (*value == "Drop")
        result.drop = true;
      else {
        fail("unknown permission");
        return {};
      }
    }
    if (result.copy && !result.drop) {
      fail("Copy requires Drop");
      return {};
    }
    return result;
  }
  std::optional<Permissions> leafPermissions(StringRef spelling) {
    auto found = nativeLeaves.find(spelling.str());
    if (found != nativeLeaves.end())
      return found->second.permissions;
    auto type = protocol::parseBoundType(spelling, false, 0, &typeBudget);
    if (!type) {
      consumeError(type.takeError());
      if (!typeBudget.remaining)
        failure = error("source.limit", "interface leaf type budget exceeded");
      else
        fail("invalid logical leaf type");
      return {};
    }
    auto policy = protocol::nativeTypePolicy(*type);
    if (!policy || type->spelling() != spelling) {
      fail("noncanonical or unsupported logical leaf type");
      return {};
    }
    Permissions result{protocol::duplicable(*type),
                       protocol::discardable(*type)};
    nativeLeaves.emplace(
        spelling.str(),
        NativeLeaf{result, policy->shared, policy->constructible, policy->total,
                   protocol::nativeSetupType(*type),
                   type->kind == "verifier_key", type->kind == "prover_key"});
    return result;
  }
  bool sameFields(ArrayRef<InterfaceField> a, ArrayRef<InterfaceField> b) {
    if (!charge(a.size() + 1) || a.size() != b.size())
      return false;
    for (unsigned i = 0; i < a.size(); ++i)
      if (a[i].name != b[i].name || a[i].offset != b[i].offset ||
          a[i].schema != b[i].schema || a[i].maximumRows != b[i].maximumRows)
        return false;
    return true;
  }
  bool sameSchema(const InterfaceSchema &a, const InterfaceSchema &b) {
    if (!charge(a.leaves.size() + a.alternatives.size() + 1) ||
        a.kind != b.kind || a.type != b.type || a.custody != b.custody ||
        a.constructible != b.constructible ||
        !(a.permissions == b.permissions) || a.leaves != b.leaves ||
        a.oracle != b.oracle || a.maximum != b.maximum ||
        a.oracleData != b.oracleData ||
        a.alternatives.size() != b.alternatives.size() ||
        !sameFields(a.fields, b.fields))
      return false;
    for (unsigned i = 0; i < a.alternatives.size(); ++i)
      if (a.alternatives[i].name != b.alternatives[i].name ||
          !sameFields(a.alternatives[i].fields, b.alternatives[i].fields))
        return false;
    return true;
  }
  bool fields(const json::Array &array, ArrayRef<std::string> leaves,
              unsigned start, unsigned depth, Permissions parent,
              std::vector<InterfaceField> &result) {
    unsigned offset = start;
    std::set<std::string> names;
    std::optional<bool> positional;
    for (const auto &item : array) {
      if (!charge(1))
        return false;
      auto *obj = object(item, {"name", "offset", "schema"});
      if (!obj)
        return false;
      auto name = text(*obj, "name", limits.identifierBytes);
      auto at = natural(*obj, "offset");
      if (!name || !at)
        return false;
      bool numbered = llvm::all_of(*name, isDigit);
      if (!positional)
        positional = numbered;
      if (numbered != *positional ||
          (numbered ? *name != std::to_string(result.size())
                    : !isSourceIdentifier(*name)) ||
          !names.insert(name->str()).second || *at != offset)
        return fail("invalid field name or noncontiguous field offset");
      auto *childObject = obj->getObject("schema");
      auto *childLeaves =
          childObject ? childObject->getArray("leaves") : nullptr;
      if (!childLeaves || offset > leaves.size() ||
          childLeaves->size() > leaves.size() - offset)
        return fail("field slice is out of bounds");
      auto child = schema(*obj->get("schema"), depth + 1,
                          leaves.slice(offset, childLeaves->size()));
      if (!child)
        return false;
      if (child->oracle || child->kind == Type::Kind::LogicalRecord ||
          offset > leaves.size() ||
          child->leaves.size() > leaves.size() - offset ||
          !llvm::equal(child->leaves,
                       leaves.slice(offset, child->leaves.size())) ||
          !child->permissions.includes(parent))
        return fail("field leaves or permissions differ from parent");
      offset += child->leaves.size();
      result.push_back({name->str(), *at, std::move(child)});
    }
    return offset == leaves.size() || fail("fields omit native leaves");
  }
  bool logicalFields(const json::Array &array, unsigned depth,
                     std::vector<InterfaceField> &result) {
    unsigned offset = 0;
    bool hasOracle = false;
    std::set<std::string> names;
    for (const auto &item : array) {
      if (!charge(1))
        return false;
      auto *raw = item.getAsObject();
      bool bounded = raw && raw->get("maximum_rows");
      auto *obj =
          bounded ? object(item, {"name", "offset", "schema", "maximum_rows"})
                  : object(item, {"name", "offset", "schema"});
      if (!obj)
        return false;
      auto name = text(*obj, "name", limits.identifierBytes);
      auto at = natural(*obj, "offset");
      if (!name || !at || *at != offset || !isSourceIdentifier(*name) ||
          !names.insert(name->str()).second)
        return fail("logical field name, order or body offset differs");
      auto *childObject = obj->getObject("schema");
      auto *ls = childObject ? childObject->getArray("leaves") : nullptr;
      if (!ls)
        return fail("logical field schema is missing");
      std::vector<std::string> expected;
      for (const auto &leaf : *ls) {
        auto spelling = leaf.getAsString();
        if (!spelling || !charge(spelling->size() + 1))
          return fail("invalid logical field data leaf");
        expected.push_back(spelling->str());
      }
      auto child = schema(*obj->get("schema"), depth + 1, expected);
      if (!child)
        return false;
      if (child->kind == Type::Kind::LogicalRecord || child->custody ||
          !(child->permissions == Permissions{true, true}))
        return fail("nested logical record or nonshared logical field");
      std::optional<uint64_t> maximum;
      if (bounded) {
        maximum = unsignedText(*obj->get("maximum_rows"));
        if (!maximum)
          return false;
      }
      if (child->oracle) {
        auto signature = protocol::oracleKindSignature(
            child->oracle->kind, child->oracle->arguments);
        if (!signature) {
          consumeError(signature.takeError());
          return fail("logical field oracle kind is unavailable");
        }
        if (signature->staticShape("rows").has_value() == maximum.has_value())
          return fail("logical field row bound is missing or invented");
        hasOracle = true;
        ++offset;
      } else {
        if (maximum || !sharedSchema(*child))
          return fail(
              "ordinary logical fields require shared data without bounds");
        offset += child->leaves.size();
      }
      if (offset > limits.aggregateLeaves)
        return fail("logical record body exceeds the leaf limit");
      result.push_back({name->str(), *at, std::move(child), maximum});
    }
    return hasOracle || fail("logical record requires a direct handle field");
  }
  bool sharedSchema(const InterfaceSchema &value) {
    if (!charge(1 + value.leaves.size()) || value.custody || value.oracle ||
        value.kind == Type::Kind::LogicalRecord ||
        !(value.permissions == Permissions{true, true}))
      return false;
    for (const auto &leaf : value.leaves) {
      const auto &policy = nativeLeaves.at(leaf);
      if (!policy.participants || !policy.total)
        return false;
    }
    for (const auto &field : value.fields)
      if (!sharedSchema(*field.schema))
        return false;
    for (const auto &arm : value.alternatives)
      for (const auto &field : arm.fields)
        if (!sharedSchema(*field.schema))
          return false;
    return true;
  }
  bool shape(const InterfaceSchema &value) {
    using K = Type::Kind;
    bool nominal = value.kind == K::Record || value.kind == K::Variant ||
                   value.kind == K::Associated;
    if (value.kind == K::Oracle || value.kind == K::OracleSequence)
      return (value.oracle && value.oracleData &&
              value.maximum.has_value() == (value.kind == K::OracleSequence) &&
              value.leaves.empty() && value.fields.empty() &&
              value.alternatives.empty() && !value.custody &&
              !value.constructible &&
              value.permissions == Permissions{true, true}) ||
             fail("oracle schemas require a complete logical handle or "
                  "sequence");
    if (value.kind == K::LogicalRecord)
      return (!value.oracle && !value.oracleData && !value.maximum &&
              value.leaves.empty() && !value.custody && !value.constructible &&
              value.permissions == Permissions{true, true} &&
              !value.fields.empty() && value.alternatives.empty()) ||
             fail("logical record requires its complete nominal field schema");
    if (value.custody && !nominal)
      return fail("custody requires a nominal type");
    if (value.kind == K::Variant)
      return !value.alternatives.empty() ||
             fail("variant alternatives missing");
    if (!value.alternatives.empty())
      return fail("alternatives require a variant type");
    if (value.kind == K::Associated)
      return (value.fields.size() == 1 && value.fields[0].name == "value") ||
             fail("associated representation requires one value field");
    if ((value.kind == K::Record || value.kind == K::Tuple ||
         value.kind == K::Array) &&
        value.fields.empty() && value.leaves.size() != unsigned(value.custody))
      return fail("empty product hides native data");
    if (value.kind == K::Record) {
      for (const auto &field : value.fields)
        if (!isSourceIdentifier(field.name))
          return fail("record fields require identifiers");
      return true;
    }
    if (value.kind == K::Tuple || value.kind == K::Array) {
      for (unsigned i = 0; i < value.fields.size(); ++i) {
        if (value.fields[i].name != std::to_string(i))
          return fail("structural product fields require positional indices");
        if (value.kind == K::Array && value.fields[i].schema->identity !=
                                          value.fields[0].schema->identity)
          return fail("array elements have different types");
      }
      return true;
    }
    if (!value.fields.empty())
      return fail("scalar schema has product fields");
    if (value.kind == K::Unit)
      return value.leaves.empty() || fail("unit schema has native data");
    if (value.leaves.size() != 1)
      return fail("scalar schema requires exactly one leaf");
    auto leafKind = protocol::typeKind(value.leaves[0]);
    bool matched =
        value.kind == K::Boolean ? leafKind == "bool"
        : value.kind == K::Index ? leafKind == "index"
        : value.kind == K::Field ? leafKind == "field"
        : value.kind == K::Group
            ? leafKind == "group"
            : value.kind == K::Builtin &&
                  (leafKind == "vector" || leafKind == "matrix" ||
                   leafKind == "groups" || leafKind == "indices" ||
                   leafKind == "bytes" || leafKind == "shake128_state" ||
                   leafKind == "quotient_matrix" || leafKind == "polynomial" ||
                   leafKind == "table" || leafKind == "point" ||
                   leafKind == "round" || leafKind == "sequence" ||
                   leafKind == "field_array" || leafKind == "commitment" ||
                   leafKind == "commitments" || leafKind == "proof" ||
                   leafKind == "prover_key" || leafKind == "verifier_key" ||
                   leafKind == "opening_state" || leafKind == "opening_states");
    return matched || fail("logical kind differs from native leaf kind");
  }
  std::optional<uint64_t> unsignedText(const json::Value &value) {
    auto text = value.getAsString();
    uint64_t result;
    if (!text || text->empty() || text->size() > 20 ||
        (text->size() > 1 && text->front() == '0') ||
        llvm::any_of(*text, [](char c) { return c < '0' || c > '9'; }) ||
        text->getAsInteger(10, result)) {
      fail("expected a canonical unsigned 64-bit decimal string");
      return {};
    }
    return result;
  }
  std::optional<InterfaceOracle> oracleDescriptor(const json::Value &value) {
    auto *obj = object(value, {"kind", "arguments"});
    if (!obj)
      return {};
    auto kind = text(*obj, "kind");
    auto *arguments = array(*obj, "arguments");
    if (!kind || !arguments || arguments->size() > 2)
      return fail("invalid closed oracle descriptor"), std::nullopt;
    InterfaceOracle result{kind->str(), {}};
    for (const auto &argument : *arguments) {
      auto *pair = argument.getAsArray();
      if (!pair || pair->size() != 2)
        return fail("invalid oracle kind argument"), std::nullopt;
      if ((*pair)[0].getAsString() == "nat") {
        auto natural = unsignedText((*pair)[1]);
        if (!natural)
          return {};
        result.arguments.push_back(
            protocol::TypeArgument::naturalArgument(*natural));
      } else if ((*pair)[0].getAsString() == "type") {
        auto text = (*pair)[1].getAsString();
        if (!text || !charge(text->size() + 1))
          return fail("invalid oracle row type"), std::nullopt;
        auto type = protocol::parseBoundType(*text, false, 0, &typeBudget);
        if (!type) {
          consumeError(type.takeError());
          if (!typeBudget.remaining)
            failure = error("source.limit", "oracle row type budget exceeded");
          return fail("invalid oracle row type"), std::nullopt;
        }
        if (type->spelling() != *text)
          return fail("noncanonical oracle row type"), std::nullopt;
        result.arguments.push_back(protocol::TypeArgument::typeArgument(*type));
      } else
        return fail("unknown oracle argument sort"), std::nullopt;
    }
    auto signature =
        protocol::oracleKindSignature(result.kind, result.arguments);
    if (!signature) {
      consumeError(signature.takeError());
      return fail("unadmitted oracle kind"), std::nullopt;
    }
    return result;
  }
  std::shared_ptr<const InterfaceSchema>
  schema(const json::Value &value, unsigned depth,
         ArrayRef<std::string> expected) {
    if (depth > limits.typeDepth) {
      failure = error("source.limit", "interface schema depth exceeded");
      return {};
    }
    if (!charge(1))
      return {};
    auto *raw = value.getAsObject();
    bool sequence = raw && raw->getString("kind") == "oracle_sequence";
    bool oracle = sequence || (raw && raw->getString("kind") == "oracle");
    auto *obj =
        sequence ? object(value, {"kind", "identity", "type", "custody",
                                  "constructible", "permissions", "fields",
                                  "alternatives", "leaves", "oracle",
                                  "data_schema", "maximum"})
        : oracle
            ? object(value, {"kind", "identity", "type", "custody",
                             "constructible", "permissions", "fields",
                             "alternatives", "leaves", "oracle", "data_schema"})
            : object(value,
                     {"kind", "identity", "type", "custody", "constructible",
                      "permissions", "fields", "alternatives", "leaves"});
    if (!obj)
      return {};
    auto type = text(*obj, "type"), kindName = text(*obj, "kind"),
         identity = text(*obj, "identity", 64);
    auto custody = obj->getBoolean("custody"),
         constructible = obj->getBoolean("constructible");
    auto *perms = array(*obj, "permissions"), *fs = array(*obj, "fields"),
         *alts = array(*obj, "alternatives"), *ls = array(*obj, "leaves");
    if (!type || !kindName || !identity || !perms || !fs || !alts || !ls)
      return {};
    using K = Type::Kind;
    auto kind = StringSwitch<std::optional<K>>(*kindName)
                    .Case("boolean", K::Boolean)
                    .Case("index", K::Index)
                    .Case("field", K::Field)
                    .Case("group", K::Group)
                    .Case("unit", K::Unit)
                    .Case("tuple", K::Tuple)
                    .Case("array", K::Array)
                    .Case("record", K::Record)
                    .Case("logical_record", K::LogicalRecord)
                    .Case("variant", K::Variant)
                    .Case("associated", K::Associated)
                    .Case("builtin", K::Builtin)
                    .Case("oracle", K::Oracle)
                    .Case("oracle_sequence", K::OracleSequence)
                    .Default(std::nullopt);
    if (!kind || !hash(*identity)) {
      fail("invalid logical kind or exact type identity");
      return {};
    }
    auto caps = permissions(*perms);
    if (!caps)
      return {};
    if (!custody || !constructible || ls->size() != expected.size() ||
        ls->size() > limits.aggregateLeaves ||
        (!fs->empty() && !alts->empty())) {
      fail("invalid schema shape or custody");
      return {};
    }
    auto result = std::make_shared<InterfaceSchema>();
    result->kind = *kind;
    result->identity = identity->str();
    result->type = type->str();
    result->custody = *custody;
    result->constructible = *constructible;
    if (result->kind == K::Associated && *constructible) {
      fail("opaque associated type cannot grant external construction");
      return {};
    }
    result->permissions = *caps;
    if (sequence) {
      result->maximum = unsignedText(*obj->get("maximum"));
      if (!result->maximum)
        return {};
    }
    if (oracle) {
      result->oracle = oracleDescriptor(*obj->get("oracle"));
      if (!result->oracle)
        return {};
      auto kind = protocol::oracleKindSignature(result->oracle->kind,
                                                result->oracle->arguments);
      if (!kind) {
        consumeError(kind.takeError());
        fail("invalid oracle data association");
        return {};
      }
      auto data = kind->data;
      if (sequence)
        data = protocol::BoundType{
            "sequence", {}, {}, {protocol::TypeArgument::typeArgument(data)}};
      result->oracleData =
          schema(*obj->get("data_schema"), depth + 1, {data.spelling()});
      if (!result->oracleData || result->oracleData->kind != K::Builtin ||
          !sharedSchema(*result->oracleData))
        return fail("oracle associated data must be ordinary shared data"),
               nullptr;
    }
    unsigned index = 0;
    for (const auto &leaf : *ls) {
      auto spelling = leaf.getAsString();
      if (!spelling || *spelling != expected[index]) {
        fail("invalid schema leaf");
        return {};
      }
      if (!charge(spelling->size() + 1))
        return {};
      auto policy = leafPermissions(*spelling);
      if (!policy)
        return {};
      if (!(result->custody && index == 0) &&
          (!policy->includes(*caps) ||
           (*constructible && *kind != K::Record && *kind != K::Tuple &&
            *kind != K::Array && *kind != K::Variant &&
            !nativeLeaves.at(spelling->str()).constructible))) {
        fail("source permissions exceed native leaf permissions");
        return {};
      }
      result->leaves.push_back(spelling->str());
      ++index;
    }
    constexpr StringLiteral custodyPrefix = "resource_unit:zkl_resource_";
    unsigned start = unsigned(result->custody);
    if (start &&
        (result->leaves.empty() || caps->copy || *constructible ||
         !StringRef(result->leaves.front()).starts_with(custodyPrefix) ||
         StringRef(result->leaves.front()).drop_front(custodyPrefix.size()) !=
             *identity)) {
      fail("invalid nominal custody prefix");
      return {};
    }
    if (!alts->empty()) {
      if (result->leaves.size() != start + 1) {
        fail("variant schema requires one native variant leaf");
        return {};
      }
      auto descriptor = protocol::decodeVariant(result->leaves[start]);
      if (!descriptor || descriptor->alternatives.size() != alts->size()) {
        fail("variant alternatives differ");
        return {};
      }
      auto *nominal = descriptor->nominal.getAsArray();
      auto encoded = nominal && nominal->size() == 2 &&
                             (*nominal)[0].getAsString() == "zkc.language"
                         ? (*nominal)[1].getAsString()
                         : std::nullopt;
      if (!encoded || !charge(encoded->size() + 1)) {
        if (!failure)
          fail("variant lacks a source nominal identity");
        return {};
      }
      auto key =
          decodeNominalIdentity(*encoded, protocol::VariantSpellingBytes / 2);
      if (!key || key->empty() ||
          toHex(SHA256::hash(arrayRefFromStringRef(*key)), true) != *identity) {
        fail("variant lacks a source nominal identity");
        return {};
      }
      std::set<std::string> names;
      for (unsigned i = 0; i < alts->size(); ++i) {
        const auto &expected = descriptor->alternatives[i];
        auto *alternative = object((*alts)[i], {"name", "fields"});
        if (!alternative)
          return {};
        auto name = text(*alternative, "name", limits.identifierBytes);
        auto *payload = array(*alternative, "fields");
        if (!name || !payload)
          return {};
        if (!isSourceIdentifier(*name) || !names.insert(name->str()).second ||
            expected.label != nativeAlternativeName(i)) {
          fail("variant name, label or order differs");
          return {};
        }
        InterfaceAlternative arm{name->str(), {}};
        if (!fields(*payload, expected.payload, 0, depth, *caps, arm.fields))
          return {};
        result->alternatives.push_back(std::move(arm));
      }
    } else if (*kind == K::LogicalRecord) {
      if (!result->leaves.empty() || !logicalFields(*fs, depth, result->fields))
        return {};
    } else if (!fs->empty()) {
      if (!fields(*fs, result->leaves, start, depth, *caps, result->fields))
        return {};
    } else if (result->leaves.size() > (start ? start : 1) ||
               (!start && !result->leaves.empty() &&
                (protocol::typeKind(result->leaves[0]) == "variant" ||
                 protocol::typeKind(result->leaves[0]) == "resource_unit"))) {
      fail("aggregate schema omits field or variant structure");
      return {};
    }
    if (!shape(*result))
      return {};
    auto [found, inserted] = schemas.emplace(result->identity, result);
    if (!inserted && !sameSchema(*found->second, *result)) {
      if (!failure)
        fail("one logical type has conflicting schemas");
      return {};
    }
    return found->second;
  }
  struct PortLeaf {
    const InterfaceSchema *schema;
    const std::string *data;
    unsigned offset;
    std::optional<uint64_t> maximumRows;
  };
  bool observe(const InterfaceSchema &value, std::optional<uint64_t> maximum,
               std::vector<PortLeaf> &leaves, unsigned &offset,
               unsigned depth = 0) {
    if (!charge(1) || depth > limits.typeDepth)
      return fail("interface port traversal limit exceeded");
    if (value.kind == Type::Kind::LogicalRecord) {
      for (const auto &field : value.fields)
        if (!observe(*field.schema, field.maximumRows, leaves, offset,
                     depth + 1))
          return false;
    } else if (value.oracle) {
      leaves.push_back({&value, nullptr, offset, maximum});
      offset += 2;
    } else {
      for (const auto &data : value.leaves) {
        if (!charge(1))
          return false;
        leaves.push_back({&value, &data, offset++, {}});
      }
    }
    return offset <= limits.aggregateLeaves ||
           fail("expanded interface port exceeds the leaf limit");
  }
  bool oracleTypes(const InterfaceSchema &schema, mlir::Type dataType,
                   mlir::Type anchorType, std::optional<uint64_t> maximumRows) {
    const auto &kind = *schema.oracle;
    auto signature = protocol::oracleKindSignature(kind.kind, kind.arguments);
    if (!signature) {
      consumeError(signature.takeError());
      return fail("oracle signature unavailable");
    }
    auto nativeKind = protocol_ir::getOracleFamilyKind(anchorType);
    std::optional<uint64_t> capacity;
    if (auto sequence =
            mlir::dyn_cast<protocol_ir::OracleSequenceType>(anchorType))
      capacity = sequence.getMaximum();
    if (!nativeKind || nativeKind.getIdentity() != kind.kind ||
        capacity != schema.maximum ||
        protocol_ir::getOracleFamilyDataType(anchorType) != dataType ||
        nativeKind.getStaticShape("rows") != signature->staticShape("rows") ||
        nativeKind.getArguments().size() != kind.arguments.size() ||
        signature->staticShape("rows").has_value() == maximumRows.has_value())
      return fail(
          "oracle kind, capacity, associated data or row bound differs");
    for (auto [actual, expected] :
         zip(nativeKind.getArguments(), kind.arguments)) {
      if (expected.kind == protocol::TypeArgument::Kind::Type) {
        auto type = mlir::dyn_cast<mlir::TypeAttr>(actual);
        if (!type)
          return fail("oracle type argument sort differs");
        auto encoded = protocol::encodeBoundType(type.getValue(), false);
        if (!encoded) {
          consumeError(encoded.takeError());
          return fail("oracle type argument is not native data");
        }
        if (!(*encoded == *expected.type))
          return fail("oracle type argument differs");
      } else {
        auto natural = mlir::dyn_cast<mlir::IntegerAttr>(actual);
        if (expected.kind != protocol::TypeArgument::Kind::Nat || !natural ||
            !natural.getType().isUnsignedInteger(64) ||
            natural.getValue().getZExtValue() != expected.natural)
          return fail("oracle natural argument differs");
      }
    }
    auto expectedData = signature->data;
    if (schema.kind == Type::Kind::OracleSequence)
      expectedData = protocol::BoundType{
          "sequence",
          {},
          {},
          {protocol::TypeArgument::typeArgument(expectedData)}};
    auto data = protocol::encodeBoundType(dataType, false);
    if (!data) {
      consumeError(data.takeError());
      return fail("oracle holder component is not data");
    }
    return *data == expectedData || fail("oracle associated data differs");
  }
  bool ports(const json::Array &array, mlir::TypeRange types,
             mlir::ArrayAttr nativeRoles, std::vector<InterfacePort> &result,
             unsigned &flat) {
    std::set<std::string> names;
    for (const auto &item : array) {
      if (!charge(1))
        return false;
      auto *raw = item.getAsObject();
      auto *rawSchema = raw ? raw->getObject("schema") : nullptr;
      bool record =
          rawSchema && rawSchema->getString("kind") == "logical_record";
      bool handle =
          rawSchema && (rawSchema->getString("kind") == "oracle" ||
                        rawSchema->getString("kind") == "oracle_sequence");
      auto *obj =
          record   ? object(item, {"name", "type", "roles", "index", "native",
                                   "schema", "holder"})
          : handle ? object(item, {"name", "type", "roles", "index", "native",
                                   "schema", "holder", "maximum_rows"})
                   : object(item, {"name", "type", "roles", "index", "native",
                                   "schema"});
      if (!obj)
        return false;
      auto name = text(*obj, "name", limits.identifierBytes);
      auto type = text(*obj, "type");
      auto index = natural(*obj, "index");
      auto *rs = this->array(*obj, "roles"), *ns = this->array(*obj, "native");
      if (!name || !type || !index || !rs || !ns)
        return false;
      auto owners = roles(*rs);
      if (!owners)
        return false;
      if (flat > types.size() || ns->size() > types.size() - flat ||
          flat > nativeRoles.size() || ns->size() > nativeRoles.size() - flat)
        return fail("port slice is out of bounds");
      std::vector<std::string> expected;
      for (unsigned i = 0; i < ns->size(); ++i) {
        auto at = (*ns)[i].getAsInteger();
        if (!at || *at != flat + i)
          return fail("native port index is not contiguous");
        if (record || handle)
          continue;
        auto data = protocol::encodeBoundType(types[flat + i], false);
        if (!data) {
          consumeError(data.takeError());
          return fail("data schema binds a non-data native port");
        }
        expected.push_back(data->spelling());
      }
      auto logical = schema(*obj->get("schema"), 1, expected);
      if (!logical)
        return false;
      if (!record && !handle && owners->size() > 1 &&
          (!logical->permissions.copy ||
           llvm::any_of(logical->leaves, [&](const auto &leaf) {
             return !nativeLeaves.at(leaf).participants;
           })))
        return fail("logical port cannot have multiple participant components");
      if (!isSourceIdentifier(*name) || !names.insert(name->str()).second ||
          *index != result.size() || *type != logical->type)
        return fail("logical port name, index or type differs");
      InterfacePort port{
          name->str(), std::move(*owners), {}, std::move(logical)};
      std::vector<unsigned> receivers;
      if (record || handle) {
        auto holder = text(*obj, "holder", limits.identifierBytes);
        auto found = holder ? roleIndices.find(*holder) : roleIndices.end();
        if (found == roleIndices.end() ||
            !is_contained(port.roles, found->second) || port.roles.size() < 2)
          return fail("oracle holder is not in its role family");
        port.oracle = InterfaceOraclePort{found->second, {}};
        if (handle && !obj->get("maximum_rows")->getAsNull()) {
          port.oracle->maximumRows = unsignedText(*obj->get("maximum_rows"));
          if (!port.oracle->maximumRows)
            return false;
        }
        for (auto role : port.roles)
          if (role != port.oracle->holder)
            receivers.push_back(role);
      }
      std::vector<PortLeaf> leaves;
      unsigned count = 0;
      if (!observe(*port.schema,
                   port.oracle ? port.oracle->maximumRows : std::nullopt,
                   leaves, count) ||
          count != ns->size())
        return fail("expanded port arity differs");
      for (const auto &leaf : leaves) {
        unsigned at = flat + leaf.offset;
        if (leaf.schema->oracle) {
          if (!port.oracle ||
              !oracleTypes(*leaf.schema, types[at], types[at + 1],
                           leaf.maximumRows) ||
              !matchesRoles(nativeRoles[at], {port.oracle->holder}) ||
              !matchesRoles(nativeRoles[at + 1], receivers))
            return false;
        } else {
          auto data = protocol::encodeBoundType(types[at], false);
          if (!data) {
            consumeError(data.takeError());
            return fail("ordinary field binds a logical native component");
          }
          if (data->spelling() != *leaf.data ||
              !matchesRoles(nativeRoles[at], port.roles))
            return fail("ordinary field type or role mapping differs");
        }
      }
      for (unsigned i = 0; i < count; ++i)
        port.native.push_back(flat++);
      result.push_back(std::move(port));
    }
    return true;
  }
  Expected<std::string> schemaIdentity(const InterfaceSchema &schema) {
    if (auto found = schemaIdentities.find(&schema);
        found != schemaIdentities.end())
      return found->second;
    FramedHash hash(remaining);
    hash.frame("zkc.language.schema/0");
    hash.frame(typeKindName(schema.kind));
    hash.frame(schema.identity);
    hash.frame(schema.custody ? "1" : "0");
    hash.frame(schema.constructible ? "1" : "0");
    for (bool allowed : {schema.permissions.copy, schema.permissions.drop})
      hash.frame(allowed ? "1" : "0");
    if (schema.oracle || schema.kind == Type::Kind::LogicalRecord) {
      std::vector<PortLeaf> leaves;
      unsigned count = 0;
      if (!observe(schema, {}, leaves, count))
        return error("source.interface", "invalid logical schema identity");
      hash.frame(std::to_string(leaves.size()));
      for (const auto &leaf : leaves) {
        if (!leaf.schema->oracle) {
          hash.frame(*leaf.data);
          continue;
        }
        hash.frame("oracle");
        hash.frame(leaf.schema->oracle->kind);
        for (const auto &argument : leaf.schema->oracle->arguments)
          hash.frame(argument.spelling());
        hash.frame(leaf.schema->maximum ? std::to_string(*leaf.schema->maximum)
                                        : "");
      }
    } else {
      hash.frame(std::to_string(schema.leaves.size()));
      for (const auto &leaf : schema.leaves)
        hash.frame(leaf);
    }
    auto fields = [&](ArrayRef<InterfaceField> fields) -> Error {
      hash.frame(std::to_string(fields.size()));
      for (const auto &field : fields) {
        hash.frame(field.name);
        hash.frame(std::to_string(field.offset));
        if (field.maximumRows) {
          hash.frame("maximum_rows");
          hash.frame(std::to_string(*field.maximumRows));
        }
        auto child = schemaIdentity(*field.schema);
        if (!child)
          return child.takeError();
        hash.frame(*child);
      }
      return Error::success();
    };
    if (auto error = fields(schema.fields))
      return std::move(error);
    hash.frame(std::to_string(schema.alternatives.size()));
    for (const auto &alternative : schema.alternatives) {
      hash.frame(alternative.name);
      if (auto error = fields(alternative.fields))
        return std::move(error);
    }
    auto digest = hash.finish();
    if (!digest)
      return digest.takeError();
    schemaIdentities.emplace(&schema, *digest);
    return digest;
  }
  bool relationRecord(const json::Value &value) {
    if (!charge(1))
      return false;
    auto *obj =
        object(value, {"symbol", "inputs", "static_arguments", "definition"});
    if (!obj)
      return false;
    auto symbol = text(*obj, "symbol", limits.symbolBytes);
    auto *inputs = array(*obj, "inputs");
    auto *definitionValue = obj->get("definition");
    if (!symbol || !inputs || !definitionValue)
      return false;
    auto found = nativeRelations.find(symbol->str());
    if (found == nativeRelations.end())
      return fail("unknown or repeated relation definition");
    auto native = found->second;
    nativeRelations.erase(found);
    InterfaceRelation result;
    result.symbol = symbol->str();
    result.externalKind = native.getKind().str();
    result.key = native.getKey().str();
    result.revision = native.getRevision().str();
    auto staticArguments =
        relation::readStaticArguments(native.getStaticArguments());
    auto *exportedArguments = obj->get("static_arguments");
    if (!staticArguments) {
      failure = staticArguments.takeError();
      return false;
    }
    if (!exportedArguments || *exportedArguments != *staticArguments)
      return fail("relation typed static arguments differ");
    result.staticArguments = std::move(*staticArguments);
    unsigned flat = 0;
    std::set<std::string> names;
    std::vector<std::string> logicalTypes, logicalPurposes;
    auto types = native.getSignature().getInputs();
    for (const auto &item : *inputs) {
      if (!charge(1))
        return false;
      auto *input = object(item, {"name", "purpose", "native", "schema"});
      if (!input)
        return false;
      auto name = text(*input, "name", limits.identifierBytes),
           purpose = text(*input, "purpose");
      auto *indices = array(*input, "native");
      if (!name || !purpose || !indices)
        return false;
      if (!isSourceIdentifier(*name) || !names.insert(name->str()).second ||
          indices->empty() || flat > types.size() ||
          indices->size() > types.size() - flat)
        return fail("invalid relation formal name or native slice");
      InterfaceRelationInput port;
      port.name = name->str();
      if (*purpose == "parameter")
        port.purpose = RelationPurpose::Parameter;
      else if (*purpose == "statement")
        port.purpose = RelationPurpose::Statement;
      else if (*purpose == "witness")
        port.purpose = RelationPurpose::Witness;
      else
        return fail("unknown relation purpose");
      std::vector<std::string> expected;
      for (const auto &index : *indices) {
        if (!charge(1))
          return false;
        auto at = index.getAsInteger();
        if (!at || *at != flat ||
            mlir::cast<mlir::StringAttr>(native.getPurposes()[flat])
                    .getValue() != *purpose)
          return fail("relation native index or purpose differs");
        auto type = protocol::encodeBoundType(types[flat], false);
        if (!type) {
          consumeError(type.takeError());
          return fail("invalid relation input type");
        }
        expected.push_back(type->spelling());
        port.native.push_back(flat++);
      }
      port.schema = schema(*input->get("schema"), 1, expected);
      if (!port.schema)
        return false;
      if (!port.schema->permissions.copy || !port.schema->permissions.drop)
        return fail("relation formals require immutable data");
      auto schemaDigest = schemaIdentity(*port.schema);
      if (!schemaDigest) {
        failure = schemaDigest.takeError();
        return false;
      }
      logicalTypes.push_back(std::move(*schemaDigest));
      logicalPurposes.push_back(purpose->str());
      result.inputs.push_back(std::move(port));
    }
    if (flat != types.size())
      return fail("relation formals omit native inputs");
    auto *definition = definitionValue->getAsObject();
    auto kind = definition ? text(*definition, "kind") : std::nullopt;
    if (!kind)
      return fail("missing relation definition kind");
    if (*kind == "formula") {
      if (!object(*definitionValue, {"kind", "function"}))
        return false;
      auto function = text(*definition, "function", limits.symbolBytes);
      if (!function)
        return false;
      auto found = helpers.find(function->str());
      if (found == helpers.end() ||
          result.externalKind != "zkc.language.formula/0" ||
          result.key != result.symbol || !native.getFormulaAttr() ||
          *function != native.getFormulaAttr().getValue())
        return fail("invalid formula identity or helper");
      auto helper = found->second;
      if (helper.getFunctionType() != native.getSignature() ||
          helper.getVisibility() != mlir::SymbolTable::Visibility::Private)
        return fail("formula helper signature or visibility differs");
      auto identity = formulas.get(helper, logicalTypes, logicalPurposes);
      if (!identity) {
        failure = identity.takeError();
        return false;
      }
      if (*identity != result.revision)
        return fail("formula revision differs from mathematical definition");
      result.kind = RelationDefinition::Kind::Formula;
      result.formula = function->str();
    } else if (*kind == "opaque") {
      if (!object(*definitionValue, {"kind"}))
        return false;
      if (StringRef(result.externalKind).starts_with("zkc."))
        return fail("opaque declaration uses a source-owned identity");
      result.kind = RelationDefinition::Kind::Opaque;
    } else if (*kind == "r1cs" || *kind == "air") {
      if (!object(*definitionValue, {"kind", "asset"}))
        return false;
      auto identity = text(*definition, "asset");
      if (!identity)
        return false;
      if (!hash(*identity) || result.key != *identity ||
          result.revision != "0" ||
          result.externalKind !=
              (*kind == "r1cs" ? "zkc.relation.r1cs/0" : "zkc.relation.air/0"))
        return fail("captured relation identity differs");
      if (!charge(assets.size() + 1))
        return false;
      auto found = llvm::find_if(assets, [&](const auto &asset) {
        return asset.identity() == *identity;
      });
      if (found == assets.end() ||
          (*kind == "r1cs" ? !found->r1cs() : !found->air()))
        return fail("captured relation requires its admitted immutable asset");
      if (result.inputs.size() != 2 ||
          result.inputs[0].schema->kind != Type::Kind::Builtin ||
          result.inputs[1].schema->kind != Type::Kind::Builtin ||
          result.inputs[0].purpose != RelationPurpose::Statement ||
          result.inputs[1].purpose != RelationPurpose::Witness ||
          types.size() != 2)
        return fail("captured relation formal ABI differs");
      auto field =
          found->r1cs() ? found->r1cs()->field() : found->air()->field();
      auto count = found->r1cs() ? found->r1cs()->publicCount()
                                 : found->air()->publicInputs();
      auto statement = protocol::applyBoundType(
          "field_array", {field.str(), std::to_string(count)});
      auto witness =
          found->r1cs()
              ? protocol::applyBoundType(
                    "field_array",
                    {field.str(), std::to_string(found->r1cs()->columns())})
              : protocol::applyBoundType("matrix", {field.str()});
      if (!statement || !witness) {
        if (!statement)
          consumeError(statement.takeError());
        if (!witness)
          consumeError(witness.takeError());
        return fail("captured asset domain is not installed");
      }
      if (result.inputs[0].schema->leaves !=
              std::vector<std::string>{statement->spelling()} ||
          result.inputs[1].schema->leaves !=
              std::vector<std::string>{witness->spelling()})
        return fail("captured relation data shape differs from its asset");
      result.kind = *kind == "r1cs" ? RelationDefinition::Kind::R1CS
                                    : RelationDefinition::Kind::AIR;
      result.asset = *found;
    } else if (*kind == "bundle") {
      if (!object(*definitionValue, {"kind", "asset"}))
        return false;
      auto identity = text(*definition, "asset");
      if (!identity)
        return false;
      if (!hash(*identity) || result.key != *identity ||
          result.revision != "0" ||
          result.externalKind != "zkc.relation.bundle/0")
        return fail("captured relation identity differs");
      if (!charge(assets.size() + 1))
        return false;
      auto found = llvm::find_if(assets, [&](const auto &asset) {
        return asset.identity() == *identity;
      });
      if (found == assets.end() || !found->bundle())
        return fail("captured relation requires its admitted immutable asset");
      // The admitted bundle alone derives the formals; the decoded record and
      // the native declaration must both spell exactly that list.
      auto derived = bundleRelationFormals(*found->bundle());
      if (!charge(derived.size() + 1))
        return false;
      if (result.inputs.size() != derived.size() ||
          types.size() != derived.size())
        return fail("bundle relation formal count differs from its asset ABI");
      for (unsigned i = 0; i < derived.size(); ++i) {
        auto native = builtinLayout(derived[i].type);
        if (!native) {
          consumeError(native.takeError());
          return fail("captured asset domain is not installed");
        }
        const auto &input = result.inputs[i];
        if (input.purpose != derived[i].purpose ||
            input.schema->kind != derived[i].type.kind ||
            input.native.size() != 1 ||
            input.schema->leaves !=
                std::vector<std::string>{native->spelling()})
          return fail("bundle relation formal differs from its asset ABI");
      }
      result.kind = RelationDefinition::Kind::Bundle;
      result.asset = *found;
    } else
      return fail("unknown relation definition kind");
    std::string canonical;
    raw_string_ostream(canonical) << result.staticArguments;
    auto [identity, added] = relationIdentities.emplace(
        std::make_tuple(result.externalKind, result.key, result.revision,
                        canonical),
        view.relations.size());
    if (!added) {
      const auto &previous = view.relations[identity->second];
      if (!charge(result.inputs.size() + 1))
        return false;
      if (result.inputs.size() != previous.inputs.size())
        return fail("one relation identity has conflicting logical signatures");
      for (unsigned i = 0; i < result.inputs.size(); ++i)
        if (result.inputs[i].schema != previous.inputs[i].schema ||
            result.inputs[i].purpose != previous.inputs[i].purpose)
          return fail(
              "one relation identity has conflicting logical signatures");
    }
    relationIndices.try_emplace(result.symbol, view.relations.size());
    view.relations.push_back(std::move(result));
    return true;
  }
  std::shared_ptr<const InterfaceSchema> project(const InterfacePort &port,
                                                 const json::Array &path,
                                                 std::vector<unsigned> &indices,
                                                 std::vector<unsigned> &native,
                                                 bool anchor = false) {
    auto schema = port.schema;
    unsigned offset = 0;
    for (const auto &item : path) {
      if (!charge(1))
        return {};
      auto at = item.getAsInteger();
      if (!at || *at < 0 || uint64_t(*at) >= schema->fields.size() ||
          schema->custody || schema->kind == Type::Kind::Variant ||
          schema->kind == Type::Kind::Associated) {
        fail("selector path is not a logical product projection");
        return {};
      }
      indices.push_back(*at);
      if (schema->kind == Type::Kind::LogicalRecord) {
        // Schema field offsets count body leaves. Derive the expanded prefix
        // independently, including preceding handles and zero-leaf fields.
        std::vector<PortLeaf> prefix;
        unsigned width = 0;
        for (unsigned i = 0; i < unsigned(*at); ++i)
          if (!observe(*schema->fields[i].schema, schema->fields[i].maximumRows,
                       prefix, width))
            return {};
        offset += width;
      } else
        offset += schema->fields[*at].offset;
      schema = schema->fields[*at].schema;
    }
    if (anchor) {
      if (!port.oracle || schema->kind != Type::Kind::Oracle ||
          !schema->oracleData || offset + 1 >= port.native.size()) {
        fail("anchor selector requires one singleton oracle field");
        return {};
      }
      native.push_back(port.native[offset + 1]);
      return schema->oracleData;
    }
    if (schema->oracle || schema->kind == Type::Kind::LogicalRecord) {
      fail("logical relation selection requires a singleton anchor");
      return {};
    }
    if (offset > port.native.size() ||
        schema->leaves.size() > port.native.size() - offset) {
      fail("selector native slice is out of bounds");
      return {};
    }
    for (unsigned i = 0; i < schema->leaves.size(); ++i)
      native.push_back(port.native[offset + i]);
    return schema;
  }
  std::optional<InterfaceSelector>
  selector(const json::Value &value,
           std::shared_ptr<const InterfaceSchema> *selected = nullptr) {
    if (!charge(1))
      return {};
    auto *obj = object(value, {"direction", "port", "path", "role"});
    if (!obj)
      return {};
    auto direction = text(*obj, "direction");
    auto port = natural(*obj, "port");
    auto *path = array(*obj, "path");
    if (!direction || !port || !path)
      return {};
    if (*direction != "input" && *direction != "output")
      return fail("invalid selector direction"), std::nullopt;
    const auto &ports =
        *direction == "input" ? current->inputs : current->outputs;
    if (*port >= ports.size())
      return fail("selector port is out of bounds"), std::nullopt;
    bool anchor = obj->get("role")->getAsNull().has_value();
    unsigned owner = 0;
    if (!anchor) {
      auto role = text(*obj, "role", limits.identifierBytes);
      if (!role)
        return {};
      auto found = roleIndices.find(*role);
      if (found == roleIndices.end() ||
          !is_contained(ports[*port].roles, found->second))
        return fail("selector does not name an actual participant component"),
               std::nullopt;
      owner = found->second;
    }
    InterfaceSelector result{
        *direction == "output", *port, owner, {}, {}, anchor};
    auto schema =
        project(ports[*port], *path, result.path, result.native, anchor);
    if (!schema)
      return {};
    if (selected)
      *selected = schema;
    return result;
  }
  std::optional<InterfaceApplication> application(const json::Value &value) {
    if (!charge(1))
      return {};
    auto *obj = object(value, {"relation", "operands"});
    if (!obj)
      return {};
    auto name = text(*obj, "relation", limits.symbolBytes);
    auto *operands = array(*obj, "operands");
    if (!name || !operands)
      return {};
    auto found = relationIndices.find(*name);
    if (found == relationIndices.end()) {
      fail("unknown relation application");
      return {};
    }
    const auto &relation = view.relations[found->second];
    if (operands->size() != relation.inputs.size()) {
      fail("relation operand arity differs");
      return {};
    }
    InterfaceApplication result{found->second, {}};
    for (unsigned i = 0; i < operands->size(); ++i) {
      std::shared_ptr<const InterfaceSchema> logical;
      auto operand = selector((*operands)[i], &logical);
      if (!operand)
        return {};
      if (logical != relation.inputs[i].schema) {
        fail("relation operand logical identity or schema differs");
        return {};
      }
      result.operands.push_back(std::move(*operand));
    }
    return result;
  }
  std::optional<InterfaceClause> clauseRecord(const json::Value &value) {
    if (!charge(1))
      return {};
    auto *obj =
        object(value, {"name", "kind", "subject", "residual", "decision"});
    if (!obj)
      return {};
    auto name = text(*obj, "name", limits.identifierBytes),
         kind = text(*obj, "kind");
    if (!name || !kind)
      return {};
    if (!isSourceIdentifier(*name)) {
      fail("invalid clause name");
      return {};
    }
    InterfaceClause result;
    result.name = name->str();
    using K = SpecificationClause::Kind;
    if (*kind == "target")
      result.kind = K::Target;
    else if (*kind == "input")
      result.kind = K::Input;
    else if (*kind == "output")
      result.kind = K::Output;
    else if (*kind == "continuation")
      result.kind = K::Continuation;
    else {
      fail("unknown clause kind");
      return {};
    }
    auto subject = application(*obj->get("subject"));
    if (!subject)
      return {};
    result.subject = std::move(*subject);
    auto output = [](const auto &application) {
      return any_of(application.operands,
                    [](const auto &selector) { return selector.output; });
    };
    if (((result.kind == K::Input || result.kind == K::Continuation) &&
         output(result.subject)) ||
        (result.kind == K::Output && !output(result.subject))) {
      fail("clause input/output direction differs");
      return {};
    }
    if (obj->get("residual")->kind() != json::Value::Null) {
      if (result.kind != K::Continuation) {
        fail("unexpected residual");
        return {};
      }
      auto residual = application(*obj->get("residual"));
      if (!residual)
        return {};
      if (!output(*residual)) {
        fail("residual must bind an actual output");
        return {};
      }
      result.residual = std::move(*residual);
    } else if (result.kind == K::Continuation) {
      fail("continuation has no residual");
      return {};
    }
    if (obj->get("decision")->kind() != json::Value::Null) {
      std::shared_ptr<const InterfaceSchema> logical;
      auto decision = selector(*obj->get("decision"), &logical);
      if (!decision)
        return {};
      if (result.kind == K::Input || !decision->output ||
          logical->kind != Type::Kind::Boolean ||
          decision->native.size() != 1) {
        fail("decision must be one Boolean output");
        return {};
      }
      result.decision = std::move(*decision);
    } else if (result.kind == K::Target) {
      fail("target has no decision");
      return {};
    }
    return result;
  }

  // Decode retained closed terms as metadata only. This does not resolve,
  // admit, check, or lower source types and never invokes the source checker.
  std::optional<Type> retainedType(const json::Value &value,
                                   unsigned depth = 0) {
    if (!charge(1) || depth > limits.typeDepth)
      return fail("retained type depth or work limit exceeded"), std::nullopt;
    auto *row = value.getAsArray();
    auto tag = row && !row->empty() ? (*row)[0].getAsString() : std::nullopt;
    if (!tag)
      return fail("invalid retained closed type"), std::nullopt;
    using K = Type::Kind;
    Type result;
    const json::Array *arguments = nullptr;
    if ((*tag == "bool" || *tag == "index" || *tag == "unit") &&
        row->size() == 1)
      result.kind = *tag == "bool"    ? K::Boolean
                    : *tag == "index" ? K::Index
                                      : K::Unit;
    else if (*tag == "nat" && row->size() == 2) {
      auto number = unsignedText((*row)[1]);
      if (!number)
        return {};
      result.kind = K::Natural;
      result.dimension = Natural::constant(*number);
    } else if ((*tag == "field" || *tag == "group") && row->size() == 2 &&
               (*row)[1].getAsString()) {
      result.kind = *tag == "field" ? K::Field : K::Group;
      result.domain = (*row)[1].getAsString()->str();
    } else if ((*tag == "domain" || *tag == "asset") && row->size() == 3 &&
               (*row)[1].getAsString() && (*row)[2].getAsString()) {
      result.kind = *tag == "domain" ? K::Domain : K::Asset;
      result.sort = (*row)[1].getAsString()->str();
      result.domain = (*row)[2].getAsString()->str();
    } else if (*tag == "array" && row->size() == 3) {
      auto element = retainedType((*row)[1], depth + 1);
      auto length = unsignedText((*row)[2]);
      if (!element || !length)
        return {};
      result.kind = K::Array;
      result.dimension = Natural::constant(*length);
      result.arguments.push_back(std::move(*element));
    } else if (*tag == "tuple" && row->size() == 2) {
      result.kind = K::Tuple;
      arguments = (*row)[1].getAsArray();
      if (!arguments)
        return fail("retained tuple arguments are absent"), std::nullopt;
    } else if ((*tag == "builtin" || *tag == "formal") && row->size() == 3 &&
               (*row)[1].getAsString()) {
      auto name = *(*row)[1].getAsString();
      result.kind = *tag == "formal"            ? K::Formal
                    : name == "oracle.table"    ? K::OracleKind
                    : name == "oracle"          ? K::Oracle
                    : name == "oracle_sequence" ? K::OracleSequence
                                                : K::Builtin;
      result.domain =
          name == "oracle.table" ? "table"
          : result.kind == K::Oracle || result.kind == K::OracleSequence
              ? ""
              : name.str();
      arguments = (*row)[2].getAsArray();
      if (!arguments)
        return fail("retained builtin arguments are absent"), std::nullopt;
    } else if (*tag == "nominal" && row->size() == 4 &&
               (*row)[1].getAsString() && (*row)[2].getAsString()) {
      auto kind = StringSwitch<std::optional<K>>(*(*row)[1].getAsString())
                      .Case("record", K::Record)
                      .Case("logical_record", K::LogicalRecord)
                      .Case("variant", K::Variant)
                      .Case("associated", K::Associated)
                      .Case("module", K::Module)
                      .Default(std::nullopt);
      if (!kind)
        return fail("retained nominal kind differs"), std::nullopt;
      result.kind = *kind;
      result.domain = (*row)[2].getAsString()->str();
      arguments = (*row)[3].getAsArray();
      if (!arguments)
        return fail("retained nominal arguments are absent"), std::nullopt;
    } else
      return fail("invalid retained type shape"), std::nullopt;
    if (!charge(result.domain.size() + result.sort.size()))
      return {};
    if (arguments)
      for (const auto &argument : *arguments) {
        auto type = retainedType(argument, depth + 1);
        if (!type)
          return {};
        result.arguments.push_back(std::move(*type));
      }
    return result;
  }
  std::optional<std::string> retainedIdentity(const json::Value &value) {
    auto type = retainedType(value);
    if (!type)
      return {};
    auto identity = typeIdentity(*type);
    if (!charge(identity.size()))
      return {};
    return toHex(SHA256::hash(arrayRefFromStringRef(identity)), true);
  }
  bool retainedSchemas(protocol_ir::ProtocolModuleOp module) {
    bool logical = llvm::any_of(schemas, [](const auto &item) {
      return item.second->kind == Type::Kind::LogicalRecord;
    });
    if (!logical)
      return true;
    auto declarations =
        exportDeclarationData(module->getAttr("source_declarations"));
    if (!declarations) {
      consumeError(declarations.takeError());
      return fail("logical record declaration carrier is absent");
    }
    auto *tables = declarations->getAsArray();
    if (!tables || tables->size() != 2 || !(*tables)[0].getAsArray())
      return fail("logical declaration tables differ");
    std::map<std::string, const json::Array *> records;
    // Nominal rows retain [type, resource, sealed, members]. Product members
    // are [name, type]; variant members are [alternative, product members].
    // Native payload widths cannot authenticate omitted zero-leaf members.
    for (const auto &value : *(*tables)[0].getAsArray()) {
      auto *record = value.getAsArray();
      if (!record || record->size() != 4 || !(*record)[1].getAsString() ||
          !(*record)[2].getAsBoolean() || !(*record)[3].getAsArray())
        return fail("retained record shape differs");
      auto identity = retainedIdentity((*record)[0]);
      if (!identity || !records.emplace(*identity, record).second)
        return fail("retained record identity differs or repeats");
    }
    std::set<const InterfaceSchema *> checked;
    auto matchFields = [&](const json::Array &fields,
                           ArrayRef<InterfaceField> expected) {
      if (!charge(1 + fields.size()) || fields.size() != expected.size())
        return fail("nominal schema omits private or zero-leaf fields");
      for (unsigned i = 0; i < fields.size(); ++i) {
        auto *field = fields[i].getAsArray();
        if (!field || field->size() != 2 ||
            (*field)[0].getAsString() != expected[i].name)
          return fail("retained nominal field name or order differs");
        auto identity = retainedIdentity((*field)[1]);
        if (!identity || *identity != expected[i].schema->identity)
          return fail("retained nominal field type differs");
      }
      return true;
    };
    std::function<bool(const InterfaceSchema &)> bind =
        [&](const InterfaceSchema &schema) {
          if (!charge(1) || !checked.insert(&schema).second)
            return !failure;
          if (schema.kind == Type::Kind::LogicalRecord ||
              schema.kind == Type::Kind::Record ||
              schema.kind == Type::Kind::Variant) {
            auto found = records.find(schema.identity);
            if (found == records.end())
              return fail("nominal logical field declaration is missing");
            const auto &record = *found->second;
            auto type = retainedType(record[0]);
            if (!type || type->kind != schema.kind ||
                spelling(*type) != schema.type)
              return fail("retained nominal source identity differs");
            if (record[1].getAsString() != "ordinary")
              return fail("logical declarations and their ordinary fields "
                          "cannot claim resource custody");
            const auto &members = *record[3].getAsArray();
            if (schema.kind == Type::Kind::Variant) {
              if (!charge(1 + members.size()) ||
                  members.size() != schema.alternatives.size())
                return fail("retained variant alternative count differs");
              for (unsigned i = 0; i < members.size(); ++i) {
                auto *arm = members[i].getAsArray();
                if (!arm || arm->size() != 2 ||
                    (*arm)[0].getAsString() != schema.alternatives[i].name ||
                    !(*arm)[1].getAsArray() ||
                    !matchFields(*(*arm)[1].getAsArray(),
                                 schema.alternatives[i].fields))
                  return fail("retained variant fields or order differ");
              }
            } else if (!matchFields(members, schema.fields))
              return false;
          }
          for (const auto &field : schema.fields)
            if (!bind(*field.schema))
              return false;
          for (const auto &arm : schema.alternatives)
            for (const auto &field : arm.fields)
              if (!bind(*field.schema))
                return false;
          return true;
        };
    for (const auto &item : schemas)
      if (item.second->kind == Type::Kind::LogicalRecord && !bind(*item.second))
        return false;
    return true;
  }
  bool transportAttributes(mlir::Operation &operation,
                           const InterfacePort &port,
                           ArrayRef<unsigned> mapping,
                           std::optional<uint64_t> maximum, bool binding) {
    if (!port.oracle)
      return fail("logical transport has no oriented family");
    auto mapped = [&](unsigned role) {
      return mapping.empty() ? role : mapping[role];
    };
    auto holder = operation.getAttrOfType<mlir::StringAttr>("holder");
    std::vector<unsigned> receivers;
    for (auto role : port.roles)
      if (role != port.oracle->holder)
        receivers.push_back(mapped(role));
    llvm::sort(receivers);
    if (!holder ||
        holder.getValue() != nativeRoleName(mapped(port.oracle->holder)) ||
        !matchesRoles(operation.getAttr("receivers"), receivers) ||
        operation.getAttrs().size() != (binding ? 3u : 2u))
      return fail("logical transport role family differs");
    if (!binding)
      return true;
    auto bounds = operation.getAttrOfType<mlir::DictionaryAttr>("shape_bounds");
    if (!bounds || bounds.size() != unsigned(maximum.has_value()))
      return fail("logical transport row bounds differ");
    if (maximum) {
      auto rows = bounds.getAs<mlir::IntegerAttr>("rows");
      if (!rows || !rows.getType().isUnsignedInteger(64) ||
          rows.getValue().getZExtValue() != *maximum)
        return fail("logical transport row maximum differs");
    }
    return true;
  }
  bool portBindings(ArrayRef<InterfacePort> ports, mlir::ValueRange actual,
                    ArrayRef<unsigned> mapping, mlir::Block &block,
                    mlir::Block::iterator cursor,
                    std::set<mlir::Operation *> &checked) {
    for (const auto &port : ports) {
      std::vector<PortLeaf> leaves;
      unsigned count = 0;
      if (!observe(*port.schema,
                   port.oracle ? port.oracle->maximumRows : std::nullopt,
                   leaves, count))
        return false;
      for (const auto &leaf : leaves) {
        if (!leaf.schema->oracle)
          continue;
        if (cursor == block.end() ||
            port.native[leaf.offset + 1] >= actual.size())
          return fail("logical transport input pair is missing");
        auto binding = mlir::dyn_cast<protocol_ir::OracleInputOp>(*cursor++);
        if (!binding || binding.getData() != actual[port.native[leaf.offset]] ||
            binding.getAnchor() != actual[port.native[leaf.offset + 1]] ||
            !checked.insert(binding).second ||
            !transportAttributes(*binding, port, mapping, leaf.maximumRows,
                                 true))
          return fail("logical transport input pair, order or bound differs");
      }
    }
    return true;
  }
  bool portComponents(ArrayRef<InterfacePort> ports, mlir::ValueRange actual,
                      ArrayRef<unsigned> mapping,
                      std::set<mlir::Operation *> &checked,
                      mlir::Operation &boundary) {
    SmallVector<mlir::Operation *> ordered;
    for (const auto &port : ports) {
      std::vector<PortLeaf> leaves;
      unsigned count = 0;
      if (!observe(*port.schema,
                   port.oracle ? port.oracle->maximumRows : std::nullopt,
                   leaves, count))
        return false;
      for (const auto &leaf : leaves) {
        if (!leaf.schema->oracle)
          continue;
        if (port.native[leaf.offset + 1] >= actual.size())
          return fail("logical transport component pair is missing");
        auto data = actual[port.native[leaf.offset]];
        auto anchor = actual[port.native[leaf.offset + 1]];
        auto parts = data.getDefiningOp<protocol_ir::OracleComponentsOp>();
        if (!parts || parts.getData() != data || parts.getAnchor() != anchor ||
            !checked.insert(parts).second ||
            !transportAttributes(*parts, port, mapping, {}, false))
          return fail(
              "logical transport components are unpaired, reused or reordered");
        ordered.push_back(parts);
      }
    }
    auto *previous = boundary.getPrevNode();
    for (auto *operation : llvm::reverse(ordered)) {
      if (previous != operation)
        return fail("logical component order differs from its ABI fields");
      previous = previous->getPrevNode();
    }
    return true;
  }
  bool transport(protocol_ir::ProtocolModuleOp module) {
    std::map<std::string, const InterfaceProtocol *> protocols;
    for (const auto &protocol : view.protocols)
      protocols.emplace(protocol.symbol, &protocol);
    for (auto function :
         module.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      auto found = protocols.find(function.getSymName().str());
      if (found == protocols.end())
        return fail("transport protocol schema is absent");
      const auto &protocol = *found->second;
      auto &block = function.getBody().front();
      std::set<mlir::Operation *> bindings, components;
      if (!portBindings(protocol.inputs, block.getArguments(), {}, block,
                        block.begin(), bindings))
        return false;
      bool valid = true;
      function.getBody().walk([&](mlir::Operation *operation) {
        if (!valid)
          return;
        if (!charge(1)) {
          valid = false;
          return;
        }
        if (auto call = mlir::dyn_cast<protocol_ir::ApplyOp>(operation)) {
          auto target = protocols.find(call.getCallee().str());
          if (target == protocols.end()) {
            valid = fail("transport application schema is absent");
            return;
          }
          auto roles = call->getAttrOfType<mlir::ArrayAttr>("roles");
          if (!roles || roles.size() != target->second->roles.size()) {
            valid = fail("transport application role arity differs");
            return;
          }
          std::vector<unsigned> mapping;
          for (auto attribute : roles) {
            auto name = mlir::dyn_cast<mlir::StringAttr>(attribute);
            unsigned role = 0;
            while (name && role < protocol.roles.size() &&
                   name.getValue() != nativeRoleName(role))
              ++role;
            if (!name || role == protocol.roles.size() ||
                is_contained(mapping, role)) {
              valid = fail("transport application role mapping differs");
              return;
            }
            mapping.push_back(role);
          }
          valid = portComponents(target->second->inputs, call.getOperands(),
                                 mapping, components, *call) &&
                  portBindings(target->second->outputs, call.getResults(),
                               mapping, *call->getBlock(),
                               std::next(call->getIterator()), bindings);
        } else if (auto returned =
                       mlir::dyn_cast<protocol_ir::MathematicalReturnOp>(
                           operation)) {
          valid = operation->getBlock() == &block &&
                  portComponents(protocol.outputs, returned.getOperands(), {},
                                 components, *returned);
          if (!valid)
            fail("logical return components differ");
        }
      });
      if (!valid)
        return false;
      function.getBody().walk([&](mlir::Operation *operation) {
        if (mlir::isa<protocol_ir::OracleInputOp>(operation) &&
            !bindings.count(operation))
          valid = fail("unmatched logical input binding");
        if (mlir::isa<protocol_ir::OracleComponentsOp>(operation) &&
            !components.count(operation))
          valid = fail("unmatched logical component view");
      });
      if (!valid)
        return false;
    }
    return true;
  }
  bool protocolRecord(const json::Value &value) {
    auto *obj = object(
        value, {"symbol", "roles", "inputs", "outputs", "services", "clauses"});
    if (!obj)
      return false;
    auto symbol = text(*obj, "symbol", limits.symbolBytes);
    auto *rs = array(*obj, "roles"), *ins = array(*obj, "inputs"),
         *outs = array(*obj, "outputs"), *services = array(*obj, "services"),
         *clauses = array(*obj, "clauses");
    if (!symbol || !rs || !ins || !outs || !services || !clauses)
      return false;
    auto found = nativeProtocols.find(symbol->str());
    if (found == nativeProtocols.end())
      return fail("unknown or repeated protocol definition");
    auto function = found->second;
    nativeProtocols.erase(found);
    view.protocols.push_back({});
    current = &view.protocols.back();
    current->symbol = symbol->str();
    roleIndices.clear();
    std::set<std::string> usedRoles;
    if (rs->empty() || rs->size() > 1024)
      return fail("invalid role roster size");
    for (const auto &item : *rs) {
      auto name = item.getAsString();
      if (!name || name->size() > limits.identifierBytes ||
          !isSourceIdentifier(*name) || !usedRoles.insert(name->str()).second)
        return fail("invalid or duplicate role");
      roleIndices.try_emplace(*name, current->roles.size());
      current->roles.push_back(name->str());
    }
    if (!function || function.getRoles().size() != current->roles.size())
      return fail("protocol symbol or role roster differs");
    std::vector<unsigned> roster;
    for (unsigned i = 0; i < current->roles.size(); ++i)
      roster.push_back(i);
    if (!matchesRoles(function.getRoles(), roster))
      return false;
    auto type = function.getFunctionType();
    unsigned input = 0, output = 0;
    if (!ports(*ins, type.getInputs(), function.getInputRoles(),
               current->inputs, input) ||
        !ports(*outs, type.getResults(), function.getOutputRoles(),
               current->outputs, output))
      return false;
    std::set<std::string> names;
    for (const auto &port : current->inputs)
      names.insert(port.name);
    for (const auto &item : *services) {
      if (!charge(1))
        return false;
      auto *service = object(item, {"name", "contract", "owner", "native"});
      if (!service)
        return false;
      auto name = text(*service, "name", limits.identifierBytes),
           contract = text(*service, "contract"),
           owner = text(*service, "owner", limits.identifierBytes);
      auto at = natural(*service, "native");
      if (!name || !contract || !owner || !at)
        return false;
      auto found = roleIndices.find(*owner);
      if (!isSourceIdentifier(*name) || !names.insert(name->str()).second ||
          *at != input || input >= type.getNumInputs() ||
          found == roleIndices.end())
        return fail("invalid managed service mapping");
      auto serviceType = mlir::dyn_cast<protocol_ir::ServiceReferenceType>(
          type.getInput(input));
      if (!serviceType || serviceType.getContract() != *contract)
        return fail("service contract differs");
      unsigned role = found->second;
      if (!matchesRoles(function.getInputRoles()[input], {role}))
        return false;
      current->services.push_back(
          {name->str(), contract->str(), role, input++});
    }
    if (input != type.getNumInputs() || output != type.getNumResults())
      return fail("interface omits native ports");
    std::set<std::string> clauseNames;
    for (const auto &item : *clauses) {
      auto clause = clauseRecord(item);
      if (!clause)
        return false;
      if (!clauseNames.insert(clause->name).second)
        return fail("repeated clause name");
      current->clauses.push_back(std::move(*clause));
    }
    // Independently project the logical selectors through their admitted
    // native slices. Original PIR owns the inventory and relation references.
    mlir::Builder builder(function.getContext());
    auto nativeSelector = [&](const InterfaceSelector &selector,
                              unsigned index) {
      if (selector.anchor)
        return builder.getArrayAttr(
            {builder.getStringAttr("anchor"),
             builder.getStringAttr(selector.output ? "output" : "input"),
             builder.getI64IntegerAttr(index)});
      return builder.getArrayAttr(
          {builder.getStringAttr(selector.output ? "output" : "input"),
           builder.getI64IntegerAttr(index),
           builder.getStringAttr(nativeRoleName(selector.role))});
    };
    auto nativeApplication = [&](const InterfaceApplication &application) {
      SmallVector<mlir::Attribute> operands;
      for (const auto &selector : application.operands)
        for (auto index : selector.native)
          operands.push_back(nativeSelector(selector, index));
      return builder.getArrayAttr(
          {mlir::FlatSymbolRefAttr::get(
               function.getContext(),
               view.relations[application.relation].symbol),
           builder.getArrayAttr(operands)});
    };
    SmallVector<mlir::Attribute> retained;
    for (const auto &clause : current->clauses) {
      auto cost = [](const InterfaceApplication &application) {
        uint64_t work = 1;
        for (const auto &selector : application.operands)
          work += 1 + selector.native.size();
        return work;
      };
      if (!charge(1 + cost(clause.subject) +
                  (clause.residual ? cost(*clause.residual) : 0)))
        return false;
      using K = SpecificationClause::Kind;
      StringRef kind = clause.kind == K::Target   ? "target"
                       : clause.kind == K::Input  ? "input"
                       : clause.kind == K::Output ? "output"
                                                  : "continuation";
      mlir::Attribute residual = builder.getUnitAttr(),
                      decision = builder.getUnitAttr();
      if (clause.residual)
        residual = nativeApplication(*clause.residual);
      if (clause.decision)
        decision =
            nativeSelector(*clause.decision, clause.decision->native.front());
      retained.push_back(builder.getArrayAttr(
          {builder.getStringAttr(kind), builder.getStringAttr(clause.name),
           nativeApplication(clause.subject), residual, decision}));
    }
    auto native = function.getContractsAttr();
    if ((!native && !retained.empty()) ||
        (native && native != builder.getArrayAttr(retained)))
      return fail("declaration contracts differ from original PIR");
    return true;
  }

  bool setups(const json::Value &value) {
    const auto *slots = value.getAsArray();
    if (!slots || slots->size() > 64)
      return fail("invalid setup slot array");
    const auto &protocol = view.selectedProtocol();
    std::set<unsigned> expected;
    std::set<unsigned> verifierKeys, covered;
    for (unsigned p = 0; p < protocol.inputs.size(); ++p) {
      const auto &input = protocol.inputs[p];
      if (input.oracle)
        continue;
      for (unsigned i = 0; i < input.native.size(); ++i) {
        if (!charge(1))
          return false;
        const auto &leaf = nativeLeaves.at(input.schema->leaves[i]);
        if (view.proof && leaf.proverKey &&
            is_contained(input.roles, view.proof->verifier))
          return fail("proof prover keys must stay with the prover");
        if (leaf.setup)
          expected.insert(input.native[i]);
        if (leaf.verifierKey) {
          if (input.schema->kind != Type::Kind::Builtin ||
              input.native.size() != 1)
            return fail("key initialization requires a whole builtin port");
          verifierKeys.insert(input.native[i]);
        }
      }
    }
    if (view.proof && verifierKeys.size() > 64)
      return fail("proof verifier key limit exceeded");
    std::set<std::string> names;
    for (const auto &item : *slots) {
      const auto *obj = object(item, {"name", "inputs"});
      if (!obj)
        return false;
      auto name = text(*obj, "name", limits.identifierBytes);
      auto *inputs = array(*obj, "inputs");
      if (!name || !inputs)
        return false;
      if (!isSourceIdentifier(*name) || !names.insert(name->str()).second ||
          inputs->empty())
        return fail("invalid, duplicate or empty setup slot");
      InterfaceSetup slot{name->str(), {}};
      bool publicVerifier = false;
      for (const auto &value : *inputs) {
        if (!charge(1))
          return false;
        auto *input = object(value, {"port", "path"});
        if (!input)
          return false;
        auto port = natural(*input, "port");
        auto *path = array(*input, "path");
        if (!port || !path)
          return false;
        if (*port >= protocol.inputs.size())
          return fail("setup selector input is absent");
        InterfaceEntryInput selected{*port, {}, {}};
        if (!project(protocol.inputs[*port], *path, selected.path,
                     selected.native))
          return false;
        bool nonempty = false;
        for (unsigned index : selected.native) {
          if (!charge(1))
            return false;
          if (!expected.count(index))
            continue;
          nonempty = true;
          if (!covered.insert(index).second)
            return fail("setup selectors overlap");
          if (view.proof && verifierKeys.count(index)) {
            if (!is_contained(view.proof->publicInputs, *port) ||
                !is_contained(protocol.inputs[*port].roles,
                              view.proof->verifier))
              return fail("proof setup keys must be public verifier inputs");
            publicVerifier = true;
          }
        }
        if (!nonempty)
          return fail("setup selector contains no setup-bearing input");
        slot.inputs.push_back(std::move(selected));
      }
      if (view.proof && !publicVerifier)
        return fail("proof setup slot requires a public verifier key");
      view.setups.push_back(std::move(slot));
    }
    return covered.size() == expected.size() ||
           fail("setup-bearing inputs require exactly one setup slot");
  }
  bool job(const json::Value &value) {
    auto *header = value.getAsObject();
    if (!header)
      return fail("Entry job must be an object");
    auto kind = text(*header, "kind");
    if (!kind)
      return false;
    if (*kind == "run")
      return bool(object(value, {"kind"}));
    auto *obj =
        object(value, {"kind", "prover", "verifier", "public", "acceptance",
                       "completion", "target", "construction"});
    if (!obj || *kind != "proof")
      return fail("unknown Entry job");
    current = &view.protocols[view.selected];
    roleIndices.clear();
    for (unsigned i = 0; i < current->roles.size(); ++i)
      roleIndices.try_emplace(current->roles[i], i);
    auto prover = text(*obj, "prover"), verifier = text(*obj, "verifier");
    auto *publicInputs = array(*obj, "public");
    if (!prover || !verifier || !publicInputs)
      return false;
    auto p = roleIndices.find(*prover), v = roleIndices.find(*verifier);
    if (current->roles.size() != 2 || p == roleIndices.end() ||
        v == roleIndices.end() || p == v)
      return fail("proof Entry requires two distinct participants");
    InterfaceProofEntry proof;
    proof.prover = p->second;
    proof.verifier = v->second;
    for (const auto &input : *publicInputs) {
      if (!charge(1))
        return false;
      auto index = input.getAsInteger();
      if (!index || *index < 0 || uint64_t(*index) >= current->inputs.size() ||
          (!proof.publicInputs.empty() &&
           uint64_t(*index) <= proof.publicInputs.back()))
        return fail("invalid public logical input index");
      proof.publicInputs.push_back(*index);
    }
    std::vector<unsigned> required;
    for (unsigned i = 0; i < current->inputs.size(); ++i) {
      if (!charge(current->inputs[i].roles.size() + 1))
        return false;
      if (is_contained(current->inputs[i].roles, proof.verifier))
        required.push_back(i);
    }
    if (required != proof.publicInputs)
      return fail("public policy differs from verifier data ports");
    std::shared_ptr<const InterfaceSchema> logical;
    auto acceptance = selector(*obj->get("acceptance"), &logical);
    if (!acceptance)
      return false;
    if (!acceptance->output || acceptance->role != proof.verifier ||
        logical->kind != Type::Kind::Boolean || acceptance->native.size() != 1)
      return fail("Entry acceptance must be one verifier Boolean output");
    proof.acceptance = std::move(*acceptance);
    if (obj->get("completion")->kind() != json::Value::Null) {
      auto completion = selector(*obj->get("completion"), &logical);
      if (!completion)
        return false;
      if (!completion->output || completion->role != proof.prover ||
          logical->kind != Type::Kind::Boolean ||
          completion->native.size() != 1)
        return fail("Entry completion must be one prover Boolean output");
      proof.completion = std::move(*completion);
    }
    const auto &construction = *obj->get("construction");
    auto *constructionObject = construction.getAsObject();
    if (!constructionObject)
      return fail("Entry construction must be an object");
    auto constructionKind = text(*constructionObject, "kind");
    auto format = text(*constructionObject, "format");
    auto parsedFormat =
        format ? protocol::parseProofFormat(*format) : std::nullopt;
    if (!constructionKind || !parsedFormat)
      return fail("unknown Entry proof format");
    proof.format = *parsedFormat;
    auto readServices = [&]() {
      auto *services = array(*constructionObject, "services");
      if (!services || services->empty() ||
          services->size() > current->services.size())
        return fail("construction requires verifier service inputs");
      for (const auto &value : *services) {
        auto service = value.getAsInteger();
        if (!service || *service < 0 ||
            uint64_t(*service) >= current->services.size() ||
            (!proof.services.empty() &&
             proof.services.back() >= uint64_t(*service)) ||
            current->services[*service].owner != proof.verifier)
          return fail("construction services must select verifier inputs in "
                      "original order");
        proof.services.push_back(unsigned(*service));
      }
      return true;
    };
    if (*constructionKind == "authored") {
      if (!object(construction, {"kind", "format"}))
        return false;
    } else if (*constructionKind == "fiat_shamir") {
      if (!object(construction, {"kind", "format", "suite", "services"}))
        return false;
      auto suite = text(*constructionObject, "suite");
      if (!readServices())
        return false;
      if (!suite)
        return false;
      if (proof.format != protocol::ProofFormat::Native ||
          proof.services.size() != 1 ||
          protocol::nativeChallengeField(*suite).empty() ||
          protocol::nativeChallengeField(*suite) !=
              protocol::randomServiceField(
                  current->services[proof.services.front()].contract))
        return fail("construction suite or verifier service differs");
      proof.construction = ProofEntry::Construction::FiatShamir;
      proof.suite = suite->str();
    } else if (*constructionKind == "derived") {
      if (!object(construction,
                  {"kind", "format", "suite", "services", "symbol"}))
        return false;
      auto symbol = text(*constructionObject, "symbol");
      if (!readServices())
        return false;
      std::string suite;
      if (constructionObject->get("suite")->kind() != json::Value::Null) {
        auto name = text(*constructionObject, "suite");
        if (!name)
          return false;
        suite = name->str();
      }
      if (!symbol)
        return fail("construction selection or verifier service differs");
      auto found = nativeConstructions.find(symbol->str());
      if (found == nativeConstructions.end())
        return fail("construction record differs");
      mlir::SymbolTableCollection symbols;
      auto resolved = protocol::resolveConstructionPlan(found->second, symbols);
      if (!resolved) {
        consumeError(resolved.takeError());
        return fail("invalid construction record");
      }
      const auto &plan = resolved->plan;
      SmallVector<unsigned> selectedServices;
      for (auto service : proof.services)
        selectedServices.push_back(current->services[service].native);
      if (resolved->definitions.size() != nativeConstructions.size() ||
          plan.codec.has_value() !=
              (proof.format == protocol::ProofFormat::RawBytes) ||
          plan.target.getValue() != current->symbol || plan.suite != suite ||
          plan.services != selectedServices)
        return fail("construction record differs");
      proof.construction = ProofEntry::Construction::Derived;
      proof.selectedConstruction = symbol->str();
      proof.suite = suite;
    } else
      return fail("unknown Entry construction");
    if (proof.construction != ProofEntry::Construction::Derived &&
        !nativeConstructions.empty())
      return fail("unselected construction record");
    if (obj->get("target")->kind() != json::Value::Null) {
      auto target = text(*obj, "target", limits.identifierBytes);
      if (!target)
        return false;
      for (unsigned i = 0; i < current->clauses.size(); ++i) {
        if (!charge(1))
          return false;
        if (current->clauses[i].name == *target)
          proof.target = i;
      }
      if (!proof.target)
        return fail("selected target is absent");
      const auto &clause = current->clauses[*proof.target];
      if (clause.kind != SpecificationClause::Kind::Target ||
          !clause.decision || clause.decision->role != proof.verifier ||
          clause.decision->port != proof.acceptance.port ||
          clause.decision->path != proof.acceptance.path)
        return fail("selected target decision differs from Entry acceptance");
      const auto &relation = view.relations[clause.subject.relation];
      for (auto [operand, input] :
           zip(clause.subject.operands, relation.inputs)) {
        if (!charge(current->inputs.size() + 1))
          return false;
        if (operand.output)
          return fail("exported target requires Entry input operands");
        const auto &port = current->inputs[operand.port];
        bool visible =
            operand.anchor
                ? port.oracle && port.oracle->holder == proof.verifier
                : is_contained(port.roles, proof.verifier);
        if ((input.purpose == RelationPurpose::Witness) == visible)
          return fail(
              "target purpose differs from verifier input availability");
      }
    }
    view.proof = std::move(proof);
    return true;
  }
  bool statements(protocol_ir::ProtocolModuleOp module) {
    const auto *proof = view.proof ? &*view.proof : nullptr;
    const auto &selected = view.protocols[view.selected];
    unsigned count = 0;
    for (auto function :
         module.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      for (auto &op : function.getBody().front()) {
        if (!charge(1 + op.getNumOperands()))
          return false;
        auto statement = mlir::dyn_cast<protocol_ir::StatementOp>(op);
        if (!statement)
          continue;
        bool entryPrefix =
            llvm::all_of(llvm::make_range(function.getBody().front().begin(),
                                          op.getIterator()),
                         [](mlir::Operation &prefix) {
                           return mlir::isa<protocol_ir::OracleInputOp>(prefix);
                         });
        if (!entryPrefix || !proof || !proof->target ||
            function.getSymName() != selected.symbol || ++count != 1)
          return fail("unexpected native Entry statement");
        const auto &clause = selected.clauses[*proof->target];
        const auto &relation = view.relations[clause.subject.relation];
        if (!statement.getTargetAttr() ||
            statement.getTargetAttr().getValue() != clause.name ||
            statement.getRelation() != relation.symbol ||
            statement.getAcceptance() != proof->acceptance.native.front())
          return fail(
              "native statement target, relation or acceptance differs");
        unsigned i = 0;
        for (const auto &operand : clause.subject.operands)
          for (unsigned index : operand.native) {
            if (!charge(1))
              return false;
            if (i >= statement.getInputs().size() ||
                i >= statement.getSelectors().size() ||
                statement.getInputs()[i] !=
                    function.getBody().front().getArgument(index) ||
                statement.getSelectors()[i] !=
                    mlir::StringAttr::get(function.getContext(),
                                          operand.anchor
                                              ? "anchor"
                                              : nativeRoleName(operand.role)))
              return fail("native statement operands or participants differ");
            ++i;
          }
        if (i != statement.getInputs().size() ||
            i != statement.getSelectors().size())
          return fail("native statement has extra operands or selectors");
      }
    }
    return count == unsigned(proof && proof->target) ||
           fail("native Entry statement omitted");
  }
  std::shared_ptr<const InterfaceSchema> hostSchema(const json::Value &value) {
    std::vector<std::string> leaves;
    auto *obj = value.getAsObject();
    auto *ls = obj ? obj->getArray("leaves") : nullptr;
    if (obj && obj->get("oracle")) {
      fail("logical oracle handles require realization before Host use");
      return {};
    }
    if (!ls) {
      fail("missing Host schema leaves");
      return {};
    }
    for (const auto &v : *ls) {
      auto text = v.getAsString();
      if (!text) {
        fail("invalid Host leaf");
        return {};
      }
      leaves.push_back(text->str());
    }
    return schema(value, 0, leaves);
  }
  bool host(const json::Value &value, mlir::ModuleOp module, StringRef digest) {
    auto *obj = object(value, {"format", "capture", "original", "toolchain",
                               "entry", "selection", "functions", "protocols",
                               "relations", "setups"});
    if (!obj || obj->getString("format") != "zkc.language-interface/0" ||
        obj->getString("original") != digest ||
        obj->getString("toolchain") != compilerToolchainIdentity())
      return fail("Host interface identity differs");
    for (StringRef key : {"capture", "original", "toolchain", "entry"})
      if (!obj->getString(key))
        return fail("Host interface identity is absent");
    if (!hash(*obj->getString("capture")))
      return fail("invalid Host capture identity");
    for (StringRef key : {"protocols", "relations", "setups"})
      if (!obj->getArray(key) || !obj->getArray(key)->empty())
        return fail("Host interface has protocol selection metadata");
    auto *selection = obj->getObject("selection");
    if (!selection || selection->size() != 2 ||
        selection->getString("kind") != "function" ||
        !selection->getString("function"))
      return fail("invalid Host selection");
    auto root = module->getAttrOfType<mlir::StringAttr>("entry.root");
    if (!root || module->getAttrs().size() != 1 ||
        root.getValue() != *selection->getString("function"))
      return fail("Host selected function differs");
    auto actual = readHostFunctions(module, limits);
    if (!actual) {
      failure = actual.takeError();
      return false;
    }
    auto *functions = obj->getArray("functions");
    if (!functions || functions->size() != actual->size() ||
        functions->size() > limits.instances)
      return fail("Host function inventory differs");
    view.capture = obj->getString("capture")->str();
    view.original = digest.str();
    view.toolchain = obj->getString("toolchain")->str();
    view.entry = obj->getString("entry")->str();
    view.host = InterfaceHostEntry{root.getValue().str(), {}};
    std::set<std::string> symbols;
    for (auto [i, v] : enumerate(*functions)) {
      auto *sig = object(v, {"symbol", "parameters", "result"});
      if (!sig || v != *(*actual)[i].getAsObject()->get("signature"))
        return fail("Host signature differs from actual SSA");
      auto symbol = text(*sig, "symbol", limits.symbolBytes);
      auto *parameters = array(*sig, "parameters");
      if (!symbol || !parameters || !symbols.insert(symbol->str()).second)
        return fail("invalid Host symbol");
      InterfaceFunction f;
      f.symbol = symbol->str();
      std::set<std::string> names;
      for (const auto &p : *parameters) {
        auto *parameter = object(p, {"name", "schema"});
        if (!parameter)
          return false;
        auto name = text(*parameter, "name", limits.identifierBytes);
        auto type = hostSchema(*parameter->get("schema"));
        if (!name || !type || !names.insert(name->str()).second)
          return fail("invalid Host parameter");
        f.parameters.push_back({name->str(), std::move(type)});
      }
      auto result = hostSchema(*sig->get("result"));
      if (!result)
        return false;
      f.result = std::move(result);
      view.host->functions.push_back(std::move(f));
    }
    if (!symbols.count(view.host->function))
      return fail("Host selected function is absent");
    if (auto e = checkHostFunctions(*actual, view, module, limits)) {
      failure = std::move(e);
      return false;
    }
    return true;
  }
  bool read(const json::Value &value, mlir::ModuleOp module, StringRef digest) {
    if (value.getAsObject() && value.getAsObject()->get("selection"))
      return host(value, module, digest);
    auto *obj =
        object(value, {"format", "capture", "original", "toolchain", "entry",
                       "protocol", "protocols", "relations", "job", "setups"});
    if (!obj)
      return false;
    auto format = text(*obj, "format"), capture = text(*obj, "capture"),
         original = text(*obj, "original"), toolchain = text(*obj, "toolchain"),
         entry = text(*obj, "entry",
                      limits.moduleBytes + 2 + limits.identifierBytes),
         symbol = text(*obj, "protocol", limits.symbolBytes);
    auto *protocols = array(*obj, "protocols"),
         *relations = array(*obj, "relations");
    if (!format || !capture || !original || !toolchain || !entry || !symbol ||
        !protocols || !relations)
      return false;
    if (*format != "zkc.language-interface/0" || !hash(*capture) ||
        *original != digest || *toolchain != compilerToolchainIdentity())
      return fail("interface format, original or toolchain identity differs");
    SmallVector<StringRef> entryParts;
    entry->split(entryParts, "::");
    if (entryParts.size() < 2 ||
        entry->rsplit("::").first.size() > limits.moduleBytes ||
        !all_of(entryParts, [&](StringRef part) {
          return part.size() <= limits.identifierBytes &&
                 isSourceIdentifier(part);
        }))
      return fail("invalid qualified Entry name");
    view.capture = capture->str();
    view.original = original->str();
    view.toolchain = toolchain->str();
    view.entry = entry->str();
    if (!module || !module->getAttrs().empty() ||
        !hasSingleElement(*module.getBody()))
      return fail("expected one unadorned protocol module");
    auto native = mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(
        module.getBody()->front());
    if (!native || native.getProfile() != protocol_ir::Profile::Protocol ||
        !hasSingleElement(native.getBody()))
      return fail("expected mathematical protocol profile");
    for (auto &op : native.getBody().front()) {
      if (!charge(1))
        return false;
      if (auto function = mlir::dyn_cast<protocol_ir::MathematicalOp>(op))
        nativeProtocols.emplace(function.getSymName().str(), function);
      else if (auto construction =
                   mlir::dyn_cast<protocol_ir::ConstructionOp>(op))
        nativeConstructions.emplace(construction.getSymName().str(),
                                    construction);
      else if (auto relation = mlir::dyn_cast<relation::DeclareOp>(op))
        nativeRelations.emplace(relation.getSymName().str(), relation);
      else if (auto helper = mlir::dyn_cast<mlir::func::FuncOp>(op))
        helpers.emplace(helper.getSymName().str(), helper);
    }
    if (nativeProtocols.size() != protocols->size() ||
        nativeRelations.size() != relations->size())
      return fail("interface definition inventory differs");
    for (const auto &item : *relations)
      if (!relationRecord(item))
        return false;
    bool selected = false;
    for (const auto &item : *protocols) {
      if (!protocolRecord(item))
        return false;
      if (current->symbol == *symbol) {
        view.selected = view.protocols.size() - 1;
        selected = true;
      }
    }
    if (!selected)
      return fail("selected protocol is absent");
    return retainedSchemas(native) && transport(native) &&
           job(*obj->get("job")) && setups(*obj->get("setups")) &&
           statements(native);
  }

public:
  explicit Reader(const Limits &limits, ArrayRef<Asset> assets)
      : limits(limits), remaining(limits.work), assets(assets),
        formulas(remaining, limits.irBytes) {
    (void)!!failure;
  }
  Expected<std::shared_ptr<const InterfaceSchema>>
  runSchema(const json::Value &value) {
    auto result = hostSchema(value);
    if (!result)
      return std::move(failure);
    return result;
  }
  Expected<LanguageInterface> run(const json::Value &value,
                                  mlir::ModuleOp module, StringRef digest) {
    if (!read(value, module, digest))
      return std::move(failure);
    return std::move(view);
  }
};
} // namespace
Expected<std::shared_ptr<const InterfaceSchema>>
decodeHostSchema(const json::Value &value, const Limits &limits) {
  return Reader(limits, {}).runSchema(value);
}
Expected<LanguageInterface> decodeInterface(mlir::ModuleOp module,
                                            StringRef digest,
                                            const json::Value &value,
                                            const Limits &limits,
                                            ArrayRef<Asset> assets) {
  return Reader(limits, assets).run(value, module, digest);
}
} // namespace zkc::language::detail
