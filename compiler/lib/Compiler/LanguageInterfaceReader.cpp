#include "LanguageInterface.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/Relation.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/FramedHash.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/SHA256.h"
#include <map>
#include <set>

using namespace llvm;
namespace zkc::language::detail {
namespace {
bool identifier(StringRef value) {
  return !value.empty() && (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) { return isAlnum(c) || c == '_'; });
}
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
  ArrayRef<RelationAsset> assets;
  StringMap<unsigned> relationIndices;
  std::map<std::tuple<std::string, std::string, std::string>, unsigned>
      relationIdentities;
  std::map<std::string, protocol_ir::MathematicalOp> nativeProtocols;
  std::map<std::string, relation::DeclareOp> nativeRelations;
  std::map<std::string, mlir::func::FuncOp> helpers;
  relation::FormulaIdentities formulas;
  std::map<const InterfaceSchema *, std::string> schemaIdentities;
  std::map<std::string, std::shared_ptr<const InterfaceSchema>> schemas;
  StringMap<unsigned> roleIndices;
  struct NativeLeaf {
    Permissions permissions;
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
      if (!name || name.getValue() != current->roles[roles[i]])
        return fail("native participant mapping differs");
    }
    return true;
  }
  std::optional<Permissions> permissions(const json::Array &values) {
    Permissions result;
    const StringRef order[] = {"Copy", "Drop", "Share", "Wire"};
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
      else if (*value == "Share")
        result.share = true;
      else if (*value == "Wire")
        result.wire = true;
      else {
        fail("unknown permission");
        return {};
      }
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
                       protocol::discardable(*type), policy->shared,
                       protocol::nativeMessageData(*type)};
    nativeLeaves.emplace(spelling.str(),
                         NativeLeaf{result, protocol::nativeSetupType(*type),
                                    type->kind == "verifier_key",
                                    type->kind == "prover_key"});
    return result;
  }
  bool sameFields(ArrayRef<InterfaceField> a, ArrayRef<InterfaceField> b) {
    if (!charge(a.size() + 1) || a.size() != b.size())
      return false;
    for (unsigned i = 0; i < a.size(); ++i)
      if (a[i].name != b[i].name || a[i].offset != b[i].offset ||
          a[i].schema != b[i].schema)
        return false;
    return true;
  }
  bool sameSchema(const InterfaceSchema &a, const InterfaceSchema &b) {
    if (!charge(a.leaves.size() + a.alternatives.size() + 1) ||
        a.kind != b.kind || a.type != b.type || a.custody != b.custody ||
        !(a.permissions == b.permissions) || a.leaves != b.leaves ||
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
                    : !identifier(*name)) ||
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
      if (offset > leaves.size() ||
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
  bool shape(const InterfaceSchema &value) {
    using K = Type::Kind;
    bool nominal = value.kind == K::Record || value.kind == K::Variant ||
                   value.kind == K::Associated;
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
        if (!identifier(field.name))
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
                   leafKind == "polynomial" || leafKind == "table" ||
                   leafKind == "point" || leafKind == "round" ||
                   leafKind == "sequence" || leafKind == "field_array" ||
                   leafKind == "commitment" || leafKind == "commitments" ||
                   leafKind == "proof" || leafKind == "prover_key" ||
                   leafKind == "verifier_key" || leafKind == "opening_state" ||
                   leafKind == "opening_states");
    return matched || fail("logical kind differs from native leaf kind");
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
    auto *obj =
        object(value, {"kind", "identity", "type", "custody", "permissions",
                       "fields", "alternatives", "leaves"});
    if (!obj)
      return {};
    auto type = text(*obj, "type"), kindName = text(*obj, "kind"),
         identity = text(*obj, "identity", 64);
    auto custody = obj->getBoolean("custody");
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
                    .Case("variant", K::Variant)
                    .Case("associated", K::Associated)
                    .Case("builtin", K::Builtin)
                    .Default(std::nullopt);
    if (!kind || !hash(*identity)) {
      fail("invalid logical kind or exact type identity");
      return {};
    }
    auto caps = permissions(*perms);
    if (!caps)
      return {};
    if (!custody || ls->size() != expected.size() ||
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
    result->permissions = *caps;
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
      // Source Share is a permission on logical components. For aggregates,
      // children retain it even when their explicit nominal custody is affine.
      // Actual multi-role placement is checked by native protocol admission.
      auto promised = *caps;
      if (!fs->empty() || !alts->empty())
        promised.share = false;
      if (!(result->custody && index == 0) && !policy->includes(promised)) {
        fail("source permissions exceed native leaf permissions");
        return {};
      }
      result->leaves.push_back(spelling->str());
      ++index;
    }
    constexpr StringLiteral custodyPrefix = "resource_unit:zkl_resource_";
    unsigned start = unsigned(result->custody);
    if (start &&
        (result->leaves.empty() || caps->copy || caps->wire ||
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
      if (!nominal || nominal->size() != 2 ||
          (*nominal)[0].getAsString() != "zkc.language" ||
          !(*nominal)[1].getAsString() ||
          (*nominal)[1].getAsString()->empty() ||
          toHex(
              SHA256::hash(arrayRefFromStringRef(*(*nominal)[1].getAsString())),
              true) != *identity) {
        if (!failure)
          fail("variant lacks a source nominal identity");
        return {};
      }
      for (unsigned i = 0; i < alts->size(); ++i) {
        const auto &expected = descriptor->alternatives[i];
        auto *alternative = object((*alts)[i], {"name", "fields"});
        if (!alternative)
          return {};
        auto name = text(*alternative, "name", limits.identifierBytes);
        auto *payload = array(*alternative, "fields");
        if (!name || !payload)
          return {};
        if (*name != expected.label) {
          fail("variant label or order differs");
          return {};
        }
        InterfaceAlternative arm{name->str(), {}};
        if (!fields(*payload, expected.payload, 0, depth, *caps, arm.fields))
          return {};
        result->alternatives.push_back(std::move(arm));
      }
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
  bool ports(const json::Array &array, mlir::TypeRange types,
             mlir::ArrayAttr nativeRoles, std::vector<InterfacePort> &result,
             unsigned &flat) {
    std::set<std::string> names;
    for (const auto &item : array) {
      if (!charge(1))
        return false;
      auto *obj =
          object(item, {"name", "type", "roles", "index", "native", "schema"});
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
      std::vector<std::string> expected;
      if (flat > types.size() || ns->size() > types.size() - flat)
        return fail("port slice is out of bounds");
      for (unsigned i = 0; i < ns->size(); ++i) {
        auto at = (*ns)[i].getAsInteger();
        if (!at || *at != flat + i)
          return fail("native port index is not contiguous");
        auto type = protocol::encodeBoundType(types[flat + i], false);
        if (!type) {
          consumeError(type.takeError());
          return fail("data schema binds a non-data native port");
        }
        expected.push_back(type->spelling());
      }
      auto logical = schema(*obj->get("schema"), 1, expected);
      if (!logical)
        return false;
      if (owners->size() > 1 &&
          (!logical->permissions.copy || !logical->permissions.drop ||
           !logical->permissions.share))
        return fail("shared logical port requires Copy, Drop and Share");
      if (!identifier(*name) || !names.insert(name->str()).second ||
          *index != result.size() || *type != logical->type ||
          ns->size() != logical->leaves.size())
        return fail("logical port name, index, type or native arity differs");
      InterfacePort port{
          name->str(), std::move(*owners), {}, std::move(logical)};
      for (unsigned i = 0; i < ns->size(); ++i) {
        if (!matchesRoles(nativeRoles[flat], port.roles))
          return false;
        port.native.push_back(flat++);
      }
      result.push_back(std::move(port));
    }
    return true;
  }
  Expected<std::string> schemaIdentity(const InterfaceSchema &schema) {
    if (auto found = schemaIdentities.find(&schema);
        found != schemaIdentities.end())
      return found->second;
    FramedHash hash(remaining);
    hash.frame("zkc.language.schema/1");
    hash.frame(typeKindName(schema.kind));
    hash.frame(schema.identity);
    hash.frame(schema.custody ? "1" : "0");
    for (bool allowed : {schema.permissions.copy, schema.permissions.drop,
                         schema.permissions.share, schema.permissions.wire})
      hash.frame(allowed ? "1" : "0");
    hash.frame(std::to_string(schema.leaves.size()));
    for (const auto &leaf : schema.leaves)
      hash.frame(leaf);
    auto fields = [&](ArrayRef<InterfaceField> fields) -> Error {
      hash.frame(std::to_string(fields.size()));
      for (const auto &field : fields) {
        hash.frame(field.name);
        hash.frame(std::to_string(field.offset));
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
    auto *obj = object(value, {"symbol", "inputs", "definition"});
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
      if (!identifier(*name) || !names.insert(name->str()).second ||
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
          result.externalKind != "zkc.language.formula/1" ||
          result.key != result.symbol ||
          *function != relation::formulaSymbol(result.key))
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
          result.revision != "1" ||
          result.externalKind !=
              (*kind == "r1cs" ? "zkc.relation.r1cs/1" : "zkc.relation.air/1"))
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
    } else
      return fail("unknown relation definition kind");
    auto [identity, added] = relationIdentities.emplace(
        std::make_tuple(result.externalKind, result.key, result.revision),
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
  std::shared_ptr<const InterfaceSchema>
  project(const InterfacePort &port, const json::Array &path,
          std::vector<unsigned> &indices, std::vector<unsigned> &native) {
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
      offset += schema->fields[*at].offset;
      schema = schema->fields[*at].schema;
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
    auto direction = text(*obj, "direction"),
         role = text(*obj, "role", limits.identifierBytes);
    auto port = natural(*obj, "port");
    auto *path = array(*obj, "path");
    if (!direction || !role || !port || !path)
      return {};
    if (*direction != "input" && *direction != "output") {
      fail("invalid selector direction");
      return {};
    }
    auto found = roleIndices.find(*role);
    const auto &ports =
        *direction == "input" ? current->inputs : current->outputs;
    if (*port >= ports.size() || found == roleIndices.end() ||
        !is_contained(ports[*port].roles, found->second)) {
      fail("selector does not name an actual participant component");
      return {};
    }
    InterfaceSelector result{
        *direction == "output", *port, found->second, {}, {}};
    auto schema = project(ports[*port], *path, result.path, result.native);
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
    if (!identifier(*name)) {
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
          !identifier(*name) || !usedRoles.insert(name->str()).second)
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
      if (!identifier(*name) || !names.insert(name->str()).second ||
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
      if (!identifier(*name) || !names.insert(name->str()).second ||
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
    auto *obj = object(value, {"kind", "prover", "verifier", "public",
                               "acceptance", "target", "construction"});
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
    const auto &construction = *obj->get("construction");
    auto *constructionObject = construction.getAsObject();
    if (!constructionObject)
      return fail("Entry construction must be an object");
    auto constructionKind = text(*constructionObject, "kind");
    if (!constructionKind)
      return false;
    if (*constructionKind == "authored") {
      if (!object(construction, {"kind"}))
        return false;
    } else if (*constructionKind == "fiat_shamir") {
      if (!object(construction, {"kind", "suite", "service"}))
        return false;
      auto suite = text(*constructionObject, "suite");
      auto service = natural(*constructionObject, "service");
      if (!suite || !service)
        return false;
      if (*service >= current->services.size() ||
          current->services[*service].owner != proof.verifier ||
          protocol::nativeChallengeField(*suite).empty() ||
          protocol::nativeChallengeField(*suite) !=
              protocol::randomServiceField(
                  current->services[*service].contract))
        return fail("construction suite or verifier service differs");
      proof.construction = ProofEntry::Construction::FiatShamir;
      proof.suite = suite->str();
      proof.service = *service;
    } else
      return fail("unknown Entry construction");
    for (unsigned i = 0; i < current->services.size(); ++i) {
      if (!charge(1))
        return false;
      if (current->services[i].owner == proof.verifier && proof.service != i)
        return fail("verifier service is outside the selected construction");
    }
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
        bool visible =
            is_contained(current->inputs[operand.port].roles, proof.verifier);
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
        if (!proof || !proof->target ||
            function.getSymName() != selected.symbol || ++count != 1)
          return fail("unexpected native Entry statement");
        const auto &clause = selected.clauses[*proof->target];
        const auto &relation = view.relations[clause.subject.relation];
        if (statement.getRelation() != relation.symbol ||
            statement.getAcceptance() != proof->acceptance.native.front())
          return fail("native statement relation or acceptance differs");
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
                                          selected.roles[operand.role]))
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
  bool read(const json::Value &value, mlir::ModuleOp module, StringRef digest) {
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
    if (*format != "zkc.language-interface/6" || !hash(*capture) ||
        *original != digest || *toolchain != compilerToolchainIdentity())
      return fail("interface format, original or toolchain identity differs");
    SmallVector<StringRef> entryParts;
    entry->split(entryParts, "::");
    if (entryParts.size() < 2 ||
        entry->rsplit("::").first.size() > limits.moduleBytes ||
        !all_of(entryParts, [&](StringRef part) {
          return part.size() <= limits.identifierBytes && identifier(part);
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
    return job(*obj->get("job")) && setups(*obj->get("setups")) &&
           statements(native);
  }

public:
  explicit Reader(const Limits &limits, ArrayRef<RelationAsset> assets)
      : limits(limits), remaining(limits.work), assets(assets),
        formulas(remaining, limits.irBytes) {
    (void)!!failure;
  }
  Expected<LanguageInterface> run(const json::Value &value,
                                  mlir::ModuleOp module, StringRef digest) {
    if (!read(value, module, digest))
      return std::move(failure);
    return std::move(view);
  }
};
} // namespace
Expected<LanguageInterface> decodeInterface(mlir::ModuleOp module,
                                            StringRef digest,
                                            const json::Value &value,
                                            const Limits &limits,
                                            ArrayRef<RelationAsset> assets) {
  return Reader(limits, assets).run(value, module, digest);
}
} // namespace zkc::language::detail
