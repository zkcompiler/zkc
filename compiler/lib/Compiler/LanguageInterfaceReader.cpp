#include "LanguageInterface.h"
#include "mlir/IR/Builders.h"
#include "zkc/Compiler/Host.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Instances.h"
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
  /// The retained carrier's authority rows: path to revision, none for a
  /// generated declaration. Revision-bound identities are recomputed over
  /// exactly these rows.
  std::map<std::string, std::optional<std::string>> retainedAuthorities;
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
  bool matchesRoles(mlir::Attribute attribute, ArrayRef<unsigned> roles) {
    if (!charge(roles.size() + 1))
      return false;
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
        NativeLeaf{
            result, policy->shared, policy->constructible, policy->total,
            protocol::nativeSetupType(*type),
            protocol::setupKey(type->kind) == protocol::SetupKey::Verifier,
            protocol::setupKey(type->kind) == protocol::SetupKey::Prover});
    return result;
  }
  bool sameFields(ArrayRef<InterfaceField> a, ArrayRef<InterfaceField> b) {
    if (!charge(a.size() + 1) || a.size() != b.size())
      return false;
    for (unsigned i = 0; i < a.size(); ++i)
      if (a[i].name != b[i].name || a[i].offset != b[i].offset ||
          a[i].schema != b[i].schema || a[i].maximumRows != b[i].maximumRows ||
          a[i].isPublic != b[i].isPublic || a[i].placement != b[i].placement)
        return false;
    return true;
  }
  bool sameSchema(const InterfaceSchema &a, const InterfaceSchema &b) {
    if (!charge(a.leaves.size() + a.alternatives.size() + 1) ||
        a.kind != b.kind || a.type != b.type || a.generated != b.generated ||
        a.custody != b.custody || a.sealed != b.sealed ||
        a.constructible != b.constructible ||
        !(a.permissions == b.permissions) || a.leaves != b.leaves ||
        a.oracle != b.oracle || a.maximum != b.maximum ||
        a.oracleData != b.oracleData || a.element != b.element ||
        a.roles != b.roles || a.alternatives.size() != b.alternatives.size() ||
        !sameFields(a.fields, b.fields))
      return false;
    for (unsigned i = 0; i < a.alternatives.size(); ++i)
      if (a.alternatives[i].name != b.alternatives[i].name ||
          !sameFields(a.alternatives[i].fields, b.alternatives[i].fields))
        return false;
    return true;
  }
  std::optional<std::vector<unsigned>> indices(const json::Array &values,
                                               unsigned participants,
                                               bool ordered,
                                               bool nonempty = true) {
    if (!charge(values.size() + 1))
      return {};
    std::vector<unsigned> result;
    std::set<unsigned> distinct;
    for (const auto &value : values) {
      auto index = value.getAsInteger();
      if (!index || *index < 0 || uint64_t(*index) >= participants ||
          !distinct.insert(unsigned(*index)).second ||
          (!ordered && !result.empty() && result.back() >= uint64_t(*index)))
        return fail("placement roles must be distinct, bounded and canonical"),
               std::nullopt;
      result.push_back(unsigned(*index));
    }
    if (nonempty && result.empty())
      return fail("placement roles must be nonempty"), std::nullopt;
    return result;
  }
  std::optional<ValuePlacement>
  placement(const json::Value &value, unsigned participants, unsigned depth) {
    if (depth > limits.typeDepth || !charge(1)) {
      if (!failure)
        failure = error("source.limit", "placement depth exceeded");
      return {};
    }
    auto *raw = value.getAsObject();
    auto kind = raw ? raw->getString("kind") : std::nullopt;
    if (!kind)
      return fail("missing placement kind"), std::nullopt;
    if (*kind == "data") {
      auto *obj = object(value, {"kind", "roles"});
      auto *values = obj ? array(*obj, "roles") : nullptr;
      auto roles =
          values ? indices(*values, participants, false) : std::nullopt;
      if (!roles)
        return {};
      return ValuePlacement(DataPlacement{std::move(*roles)});
    }
    if (*kind == "oracle") {
      auto *obj = object(value, {"kind", "holder", "receivers"});
      if (!obj)
        return {};
      auto holder = natural(*obj, "holder");
      auto *values = array(*obj, "receivers");
      auto receivers =
          values ? indices(*values, participants, false) : std::nullopt;
      if (!holder || !receivers)
        return {};
      if (*holder >= participants || is_contained(*receivers, *holder))
        return fail("oracle holder must be outside its receivers"),
               std::nullopt;
      return ValuePlacement(OraclePlacement{*holder, std::move(*receivers)});
    }
    if (*kind != "product")
      return fail("unknown placement kind"), std::nullopt;
    auto *obj = object(value, {"kind", "instance", "arguments", "fields"});
    if (!obj)
      return {};
    auto instance = text(*obj, "instance", 64);
    auto *arguments = array(*obj, "arguments"), *fields = array(*obj, "fields");
    auto roles =
        arguments ? indices(*arguments, participants, true) : std::nullopt;
    if (!instance || !hash(*instance) || !roles || !fields)
      return fail("invalid product placement"), std::nullopt;
    ProductPlacement result{instance->str(), std::move(*roles), {}};
    for (const auto &field : *fields) {
      auto child = placement(field, participants, depth + 1);
      if (!child)
        return {};
      result.fields.push_back(std::move(*child));
    }
    return ValuePlacement(std::move(result));
  }
  unsigned bodyWidth(const InterfaceSchema &value) {
    if (!charge(1))
      return 0;
    if (!logicalSchema(value))
      return value.leaves.size();
    if (value.oracle)
      return 1;
    unsigned width = value.custody;
    for (const auto &field : value.fields)
      width += bodyWidth(*field.schema);
    return width;
  }
  bool rawLogical(const json::Value &value, unsigned depth) {
    if (depth > limits.typeDepth || !charge(1)) {
      if (!failure)
        failure = error("source.limit", "schema category depth exceeded");
      return false;
    }
    auto *obj = value.getAsObject();
    if (!obj)
      return false;
    auto kind = obj->getString("kind");
    if (kind == "oracle" || kind == "oracle_sequence" ||
        kind == "logical_record")
      return true;
    if (kind == "array") {
      auto *element = obj->get("element");
      return element && rawLogical(*element, depth + 1);
    }
    if (kind == "tuple") {
      auto *fields = obj->getArray("fields");
      if (fields)
        for (const auto &field : *fields) {
          auto *f = field.getAsObject();
          if (f && f->get("schema") && rawLogical(*f->get("schema"), depth + 1))
            return true;
        }
    }
    return false;
  }
  std::vector<unsigned> participants(const ValuePlacement &value) {
    if (const auto *data = std::get_if<DataPlacement>(&value.value))
      return data->roles;
    if (const auto *oracle = std::get_if<OraclePlacement>(&value.value)) {
      auto result = oracle->receivers;
      result.push_back(oracle->holder);
      llvm::sort(result);
      return result;
    }
    return std::get<ProductPlacement>(value.value).arguments;
  }
  void canonicalApplications(const InterfaceSchema &schema,
                             ValuePlacement &value) {
    auto *product = std::get_if<ProductPlacement>(&value.value);
    if (!product)
      return;
    bool array = schema.kind == Type::Kind::Array;
    if (array || schema.kind == Type::Kind::Tuple)
      llvm::sort(product->arguments);
    for (unsigned i = 0; i < product->fields.size(); ++i) {
      const auto &child = array ? schema.element : schema.fields[i].schema;
      canonicalApplications(*child, product->fields[i]);
    }
  }
  bool placementSchema(const InterfaceSchema &schema,
                       const ValuePlacement &value, unsigned roster,
                       unsigned depth = 0) {
    if (depth > limits.typeDepth || !charge(1)) {
      if (!failure)
        failure = error("source.limit", "placement schema depth exceeded");
      return false;
    }
    if (auto *data = std::get_if<DataPlacement>(&value.value)) {
      if (logicalSchema(schema))
        return fail("logical schema has data placement");
      if (data->roles.size() > 1 &&
          (!schema.permissions.copy ||
           llvm::any_of(schema.leaves,
                        [&](const auto &leaf) {
                          return !nativeLeaves.at(leaf).participants;
                        }) ||
           (schema.element && !sharedSchema(*schema.element))))
        return fail("ordinary placement cannot share restricted components");
      return true;
    }
    if (std::holds_alternative<OraclePlacement>(value.value))
      return schema.oracle.has_value() ||
             fail("oracle placement requires a handle schema");
    if ((schema.kind != Type::Kind::LogicalRecord &&
         schema.kind != Type::Kind::Tuple &&
         schema.kind != Type::Kind::Array) ||
        schema.oracle)
      return fail(
          "product placement requires a distributed or structural product");
    const auto &product = std::get<ProductPlacement>(value.value);
    bool array = schema.kind == Type::Kind::Array;
    bool legacy =
        schema.kind == Type::Kind::LogicalRecord && schema.roles.empty();
    if (product.instance != schema.identity ||
        product.fields.size() != (array ? 1 : schema.fields.size()) ||
        (schema.kind == Type::Kind::LogicalRecord && !legacy &&
         product.arguments.size() != schema.roles.size()))
      return fail("product instance, role arity or field count differs");
    std::set<unsigned> childRoles;
    for (unsigned i = 0; i < product.fields.size(); ++i) {
      const auto &child = array ? schema.element : schema.fields[i].schema;
      if (!child ||
          !placementSchema(*child, product.fields[i], roster, depth + 1))
        return false;
      auto roles = participants(product.fields[i]);
      if (!charge(roles.size() + product.arguments.size() + 1))
        return false;
      for (auto role : roles) {
        if (!is_contained(product.arguments, role))
          return fail("field placement escapes the role application");
        childRoles.insert(role);
      }
      if (schema.kind == Type::Kind::LogicalRecord && !legacy) {
        if (!schema.fields[i].placement)
          return fail("distributed field formula missing");
        auto expected =
            substitutePlacement(*schema.fields[i].placement, product.arguments,
                                roster, remaining, limits.typeDepth);
        if (!expected) {
          failure = expected.takeError();
          return false;
        }
        canonicalApplications(*child, *expected);
        if (*expected != product.fields[i])
          return fail("field placement differs from declaration formula");
      }
    }
    if ((schema.kind != Type::Kind::LogicalRecord || legacy) &&
        !llvm::equal(product.arguments, childRoles))
      return fail("structural product roles differ from canonical child union");
    if (legacy) {
      // The brace profile has one explicit oriented family for all handles.
      // Remove this alternative with the corresponding Layout migration seam.
      const OraclePlacement *family = nullptr;
      for (unsigned i = 0; i < product.fields.size(); ++i) {
        if (!charge(1 + product.arguments.size()))
          return false;
        if (schema.fields[i].schema->oracle) {
          auto *actual = std::get_if<OraclePlacement>(&product.fields[i].value);
          if (!actual || (family && !(*family == *actual)))
            return fail(
                "legacy logical fields have different oriented families");
          family = actual;
        } else {
          auto *actual = std::get_if<DataPlacement>(&product.fields[i].value);
          if (!actual || actual->roles != product.arguments)
            return fail(
                "legacy metadata differs from its complete role family");
        }
      }
      if (!family || participants(ValuePlacement(*family)) != product.arguments)
        return fail("legacy logical product lacks its exact oriented family");
    }
    return true;
  }
  bool fields(const json::Array &array, ArrayRef<std::string> leaves,
              unsigned start, unsigned depth, Permissions parent,
              std::vector<InterfaceField> &result, bool logical = false,
              unsigned telescope = 0) {
    unsigned offset = start;
    std::set<std::string> names;
    std::optional<bool> positional;
    for (const auto &item : array) {
      if (!charge(1))
        return false;
      auto *raw = item.getAsObject();
      bool bounded = raw && raw->get("maximum_rows");
      auto *obj =
          bounded ? object(item, {"name", "offset", "public", "placement",
                                  "schema", "maximum_rows"})
                  : object(item,
                           {"name", "offset", "public", "placement", "schema"});
      if (!obj)
        return false;
      auto name = text(*obj, "name", limits.identifierBytes);
      auto at = natural(*obj, "offset");
      auto visible = obj->getBoolean("public");
      if (!name || !at || !visible)
        return fail("invalid field metadata");
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
      if (!childLeaves)
        return fail("missing field leaves");
      std::vector<std::string> expected;
      for (const auto &leaf : *childLeaves) {
        auto text = leaf.getAsString();
        if (!text || !charge(text->size() + 1))
          return fail("invalid field leaf");
        expected.push_back(text->str());
      }
      auto child = schema(*obj->get("schema"), depth + 1, expected);
      if (!child)
        return false;
      if ((!logical && logicalSchema(*child)) ||
          !child->permissions.includes(parent))
        return fail("field category or permissions differ from parent");
      if (!logical &&
          (offset > leaves.size() ||
           child->leaves.size() > leaves.size() - offset ||
           !llvm::equal(child->leaves,
                        leaves.slice(offset, child->leaves.size()))))
        return fail("field leaves differ from parent");
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
          return fail("oracle kind unavailable");
        }
        if (signature->staticShape("rows").has_value() == maximum.has_value())
          return fail("field row bound is missing or invented");
      } else if (maximum)
        return fail("ordinary or aggregate field has a row bound");
      std::optional<ValuePlacement> formula;
      if (telescope) {
        formula = placement(*obj->get("placement"), telescope, depth + 1);
        if (!formula ||
            !placementSchema(*child, *formula, telescope, depth + 1))
          return false;
      } else if (!obj->get("placement")->getAsNull())
        return fail("ordinary or structural field has a placement formula");
      offset += bodyWidth(*child);
      if (failure)
        return false;
      if (offset > limits.aggregateLeaves)
        return fail("product body exceeds leaf limit");
      result.push_back({name->str(), *at, std::move(child), maximum, *visible,
                        std::move(formula)});
    }
    return logical || offset == leaves.size() ||
           fail("fields omit native leaves");
  }
  bool sharedSchema(const InterfaceSchema &value) {
    if (!charge(1 + value.leaves.size()) || value.custody || value.oracle ||
        logicalSchema(value) || !(value.permissions == Permissions{true, true}))
      return false;
    for (const auto &leaf : value.leaves) {
      const auto &policy = nativeLeaves.at(leaf);
      if (!policy.participants || !policy.total)
        return false;
    }
    if (value.element && !sharedSchema(*value.element))
      return false;
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
    if (value.sealed && !nominal && value.kind != K::LogicalRecord)
      return fail("sealing requires a nominal schema");
    if (value.sealed && value.constructible)
      return fail("sealed schema cannot grant ordinary construction");
    if (value.kind == K::Oracle || value.kind == K::OracleSequence)
      return (value.roles.empty() && !value.element && value.oracle &&
              value.oracleData &&
              value.maximum.has_value() == (value.kind == K::OracleSequence) &&
              value.leaves.empty() && value.fields.empty() &&
              value.alternatives.empty() && !value.custody &&
              !value.constructible &&
              value.permissions == Permissions{true, true}) ||
             fail("oracle schemas require a complete logical handle or "
                  "sequence");
    if (value.kind == K::LogicalRecord) {
      if (value.oracle || value.oracleData || value.maximum ||
          !value.leaves.empty() || value.constructible ||
          !value.alternatives.empty() ||
          (value.custody &&
           (value.custody != value.roles.size() || value.permissions.copy)))
        return fail("invalid distributed record schema or custody arity");
      if (value.roles.empty()) {
        // Explicit current-schema transition category, never a missing-field
        // fallback. Its source admission is Semantics::logicalRecord.
        if (value.custody || !(value.permissions == Permissions{true, true}))
          return fail("legacy logical records require unrestricted custody");
        bool handle = false;
        for (const auto &field : value.fields) {
          if (!charge(1) || !isSourceIdentifier(field.name) || field.placement)
            return fail("legacy logical fields cannot declare role formulas");
          if (field.schema->oracle)
            handle = true;
          else if (!sharedSchema(*field.schema))
            return fail("legacy logical metadata must be ordinary shared data");
        }
        return handle || fail("legacy logical record requires a direct handle");
      }
      for (const auto &field : value.fields)
        if (!isSourceIdentifier(field.name) || !field.placement)
          return fail("distributed fields require declaration-local placement "
                      "formulas");
      return true;
    }
    if (!value.roles.empty())
      return fail("only distributed records declare role parameters");
    if (logicalSchema(value) &&
        (value.constructible || value.custody || !value.leaves.empty()))
      return fail("structural logical product has an ordinary data carrier");
    if (value.custody > 1 || (value.custody && !nominal))
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
      if (value.kind == K::Array && !value.element)
        return fail("array element schema missing");
      for (unsigned i = 0; i < value.fields.size(); ++i) {
        if (value.fields[i].name != std::to_string(i) ||
            !value.fields[i].isPublic)
          return fail("structural product fields require positional indices");
        if (value.kind == K::Array &&
            value.fields[i].schema->identity != value.element->identity)
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
    if (value.kind == K::Builtin)
      return !isBuiltinDataConstructor(leafKind)
                 ? fail("logical kind differs from native leaf kind")
             : !isOrdinaryBuiltinData(leafKind)
                 ? fail("builtin leaf is not ordinary Copy and Drop data")
                 : true;
    bool matched = value.kind == K::Boolean ? leafKind == "bool"
                   : value.kind == K::Index ? leafKind == "index"
                   : value.kind == K::Field
                       ? leafKind == "field"
                       : value.kind == K::Group && leafKind == "group";
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
        sequence
            ? object(value, {"kind", "identity", "type", "generated", "custody",
                             "sealed", "constructible", "permissions", "fields",
                             "alternatives", "leaves", "roles", "element",
                             "oracle", "data_schema", "maximum"})
        : oracle
            ? object(value, {"kind", "identity", "type", "generated", "custody",
                             "sealed", "constructible", "permissions", "fields",
                             "alternatives", "leaves", "roles", "element",
                             "oracle", "data_schema"})
            : object(value, {"kind", "identity", "type", "generated", "custody",
                             "sealed", "constructible", "permissions", "fields",
                             "alternatives", "leaves", "roles", "element"});
    if (!obj)
      return {};
    auto type = text(*obj, "type"), kindName = text(*obj, "kind"),
         identity = text(*obj, "identity", 64);
    auto custody = natural(*obj, "custody");
    auto constructible = obj->getBoolean("constructible");
    auto sealed = obj->getBoolean("sealed");
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
    if (!custody || !sealed || !constructible ||
        ls->size() != expected.size() || ls->size() > limits.aggregateLeaves ||
        (!fs->empty() && !alts->empty())) {
      fail("invalid schema shape or custody");
      return {};
    }
    auto result = std::make_shared<InterfaceSchema>();
    result->kind = *kind;
    result->identity = identity->str();
    result->type = type->str();
    if (!obj->get("generated")->getAsNull()) {
      auto generated = text(*obj, "generated", 64);
      if (!generated || !hash(*generated) ||
          (*kind != K::Record && *kind != K::Variant &&
           *kind != K::Associated)) {
        fail("generated-family identity requires a nominal schema");
        return {};
      }
      result->generated = generated->str();
    }
    result->custody = *custody;
    result->sealed = *sealed;
    result->constructible = *constructible;
    if (result->kind == K::Associated && *constructible) {
      fail("opaque associated type cannot grant external construction");
      return {};
    }
    result->permissions = *caps;
    if (*custody > limits.aggregateLeaves) {
      fail("schema custody count exceeds limit");
      return {};
    }
    // A nominal record's telescope is bounded by its own catalog limit, not
    // by the protocol roster's.
    auto *roleNames = array(*obj, "roles");
    if (!roleNames)
      return {};
    if (roleNames->size() > protocol::instances::recordRoleLimit) {
      fail("schema role telescope exceeds the record.roles limit");
      return {};
    }
    std::set<std::string> names;
    for (const auto &role : *roleNames) {
      auto name = role.getAsString();
      if (!name || !charge(name->size() + 1) ||
          name->size() > limits.identifierBytes || !isSourceIdentifier(*name) ||
          !names.insert(name->str()).second) {
        fail("invalid or repeated declaration role parameter");
        return {};
      }
      result->roles.push_back(name->str());
    }
    if (*kind == K::Array) {
      auto *elementObject = obj->getObject("element");
      auto *elementLeaves =
          elementObject ? elementObject->getArray("leaves") : nullptr;
      if (!elementLeaves) {
        fail("array requires an element schema");
        return {};
      }
      std::vector<std::string> expectedElement;
      for (const auto &leaf : *elementLeaves) {
        auto text = leaf.getAsString();
        if (!text || !charge(text->size() + 1)) {
          fail("invalid element leaf");
          return {};
        }
        expectedElement.push_back(text->str());
      }
      result->element =
          schema(*obj->get("element"), depth + 1, expectedElement);
      if (!result->element)
        return {};
    } else if (!obj->get("element")->getAsNull()) {
      fail("element schema requires an array");
      return {};
    }
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
      if (!(index < result->custody) &&
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
    unsigned start = result->custody;
    bool logicalProduct = rawLogical(value, depth);
    if (failure)
      return {};
    if (start && (caps->copy || *constructible ||
                  (*kind != K::LogicalRecord &&
                   (start != 1 || result->leaves.size() < start)))) {
      fail("invalid nominal custody prefix");
      return {};
    }
    if (*kind != K::LogicalRecord)
      for (unsigned i = 0; i < start; ++i)
        if (!StringRef(result->leaves[i]).starts_with(custodyPrefix) ||
            StringRef(result->leaves[i]).drop_front(custodyPrefix.size()) !=
                *identity) {
          fail("invalid nominal custody identity");
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
    } else if (!fs->empty() || *kind == K::LogicalRecord) {
      if (!fields(*fs, result->leaves, start, depth, *caps, result->fields,
                  logicalProduct, result->roles.size()))
        return {};
      bool actualLogical = logicalSchema(*result);
      if (actualLogical != logicalProduct &&
          (!result->leaves.empty() || bodyWidth(*result) != 0)) {
        fail("product logical category differs from child schemas");
        return {};
      }
      if (failure)
        return {};
      if (!actualLogical) {
        unsigned width = start;
        for (const auto &field : result->fields) {
          if (logicalSchema(*field.schema) || width > result->leaves.size() ||
              field.schema->leaves.size() > result->leaves.size() - width ||
              !llvm::equal(field.schema->leaves,
                           ArrayRef(result->leaves)
                               .slice(width, field.schema->leaves.size()))) {
            fail("ordinary product field leaves differ");
            return {};
          }
          width += field.schema->leaves.size();
        }
        if (width != result->leaves.size()) {
          fail("product native coverage differs");
          return {};
        }
      }
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
    std::string data;
    unsigned offset;
    std::optional<uint64_t> maximumRows;
    std::optional<ValuePlacement> placement;
    std::vector<unsigned> path;
    unsigned local = 0;
    bool custody = false;
  };
  bool observe(const InterfaceSchema &value, std::optional<uint64_t> maximum,
               std::vector<PortLeaf> &leaves, unsigned &offset,
               unsigned depth = 0, const ValuePlacement *placed = nullptr,
               std::vector<unsigned> path = {}) {
    if (depth > limits.typeDepth || !charge(1 + path.size())) {
      if (!failure)
        failure =
            error("source.limit", "interface port traversal limit exceeded");
      return false;
    }
    auto add = [&](std::string data, unsigned local, bool custody,
                   const ValuePlacement *placement) {
      if (!charge(data.size() + path.size() + 1))
        return false;
      leaves.push_back({&value, std::move(data), offset, maximum,
                        placement ? std::optional(*placement) : std::nullopt,
                        path, local, custody});
      offset += value.oracle ? 2 : 1;
      return offset <= limits.aggregateLeaves ||
             fail("expanded port exceeds leaf limit");
    };
    if (value.oracle)
      return add({}, 0, false, placed);
    const auto *product =
        placed ? std::get_if<ProductPlacement>(&placed->value) : nullptr;
    for (unsigned i = 0; i < value.custody; ++i) {
      std::optional<ValuePlacement> fragment;
      if (product)
        fragment = ValuePlacement(DataPlacement{{product->arguments[i]}});
      else if (placed)
        fragment = *placed;
      std::string unit = "resource_unit:zkl_resource_" + value.identity;
      if (!add(std::move(unit), i, true, fragment ? &*fragment : nullptr))
        return false;
    }
    if (!value.fields.empty() || logicalSchema(value)) {
      for (unsigned i = 0; i < value.fields.size(); ++i) {
        const auto &field = value.fields[i];
        auto childPath = path;
        childPath.push_back(i);
        const auto *childPlacement =
            product ? &product->fields[value.kind == Type::Kind::Array ? 0 : i]
                    : placed;
        if (!observe(*field.schema, field.maximumRows, leaves, offset,
                     depth + 1, childPlacement, std::move(childPath)))
          return false;
      }
    } else
      for (unsigned i = value.custody; i < value.leaves.size(); ++i)
        if (!add(value.leaves[i], i, false, placed))
          return false;
    return true;
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
      bool handle =
          rawSchema && (rawSchema->getString("kind") == "oracle" ||
                        rawSchema->getString("kind") == "oracle_sequence");
      auto *obj =
          handle ? object(item, {"name", "type", "index", "native", "schema",
                                 "placement", "components", "maximum_rows"})
                 : object(item, {"name", "type", "index", "native", "schema",
                                 "placement", "components"});
      if (!obj)
        return false;
      auto name = text(*obj, "name", limits.identifierBytes),
           type = text(*obj, "type");
      auto index = natural(*obj, "index");
      auto *ns = this->array(*obj, "native"),
           *cs = this->array(*obj, "components");
      auto *ls = rawSchema ? rawSchema->getArray("leaves") : nullptr;
      if (!name || !type || !index || !ns || !cs || !ls)
        return fail("invalid port metadata");
      if (flat > types.size() || ns->size() > types.size() - flat ||
          flat > nativeRoles.size() || ns->size() > nativeRoles.size() - flat)
        return fail("port slice is out of bounds");
      for (unsigned i = 0; i < ns->size(); ++i)
        if ((*ns)[i].getAsInteger() != int64_t(flat + i))
          return fail("native port index is not contiguous");
      std::vector<std::string> expected;
      for (const auto &leaf : *ls) {
        auto text = leaf.getAsString();
        if (!text || !charge(text->size() + 1))
          return fail("invalid port schema leaf");
        expected.push_back(text->str());
      }
      auto logical = schema(*obj->get("schema"), 1, expected);
      auto placed = placement(*obj->get("placement"), roleIndices.size(), 1);
      if (!logical || !placed ||
          !placementSchema(*logical, *placed, roleIndices.size()))
        return false;
      if (!isSourceIdentifier(*name) || !names.insert(name->str()).second ||
          *index != result.size() || *type != logical->type)
        return fail("logical port name, index or type differs");
      InterfacePort port{
          name->str(), participants(*placed), {}, std::move(logical),
          {},          std::move(*placed),    {}};
      // Derived summaries are never used to authorize individual components.
      llvm::sort(port.roles);
      if (handle) {
        auto *oracle = std::get_if<OraclePlacement>(&port.placement->value);
        if (!oracle)
          return fail("handle requires oracle placement");
        port.oracle = InterfaceOraclePort{oracle->holder, {}};
        if (!obj->get("maximum_rows")->getAsNull()) {
          port.oracle->maximumRows = unsignedText(*obj->get("maximum_rows"));
          if (!port.oracle->maximumRows)
            return false;
        }
      }
      std::vector<PortLeaf> leaves;
      unsigned count = 0;
      if (!observe(*port.schema,
                   port.oracle ? port.oracle->maximumRows : std::nullopt,
                   leaves, count, 0, &*port.placement) ||
          count != ns->size())
        return fail("expanded port arity differs");
      std::vector<InterfaceComponent> reconstructed;
      for (const auto &leaf : leaves) {
        unsigned at = flat + leaf.offset;
        if (!leaf.placement)
          return fail("native leaf placement missing");
        auto componentStart = reconstructed.size();
        auto append = [&](unsigned role, InterfaceComponentFacet facet,
                          unsigned index) {
          if (!charge(leaf.path.size() + 1))
            return false;
          reconstructed.push_back({leaf.path, leaf.local, role, facet, index});
          return true;
        };
        if (leaf.schema->oracle) {
          const auto *oracle =
              std::get_if<OraclePlacement>(&leaf.placement->value);
          if (!oracle ||
              !oracleTypes(*leaf.schema, types[at], types[at + 1],
                           leaf.maximumRows) ||
              !matchesRoles(nativeRoles[at], {oracle->holder}) ||
              !matchesRoles(nativeRoles[at + 1], oracle->receivers))
            return false;
          // Holder data precedes the canonical receiver anchor family in ABI
          // order.
          if (!append(oracle->holder, InterfaceComponentFacet::OracleData, at))
            return false;
          for (unsigned role : oracle->receivers)
            if (!append(role, InterfaceComponentFacet::OracleAnchor, at + 1))
              return false;
        } else {
          const auto *dataPlacement =
              std::get_if<DataPlacement>(&leaf.placement->value);
          auto data = protocol::encodeBoundType(types[at], false);
          if (!data) {
            consumeError(data.takeError());
            return fail("ordinary field binds a logical native component");
          }
          if (!dataPlacement || data->spelling() != leaf.data ||
              !matchesRoles(nativeRoles[at], dataPlacement->roles))
            return fail("ordinary field type or participant mapping differs");
          for (unsigned role : dataPlacement->roles)
            if (!append(role,
                        leaf.custody ? InterfaceComponentFacet::Custody
                                     : InterfaceComponentFacet::Data,
                        at))
              return false;
        }
        llvm::sort(
            MutableArrayRef(reconstructed).drop_front(componentStart),
            [](const auto &a, const auto &b) { return a.role < b.role; });
      }
      if (!charge(reconstructed.size() + cs->size() + 1) ||
          cs->size() != reconstructed.size())
        return fail("port component coverage differs");
      for (unsigned i = 0; i < cs->size(); ++i) {
        auto *component =
            object((*cs)[i], {"path", "leaf", "role", "facet", "native"});
        if (!component)
          return false;
        auto *path = this->array(*component, "path");
        auto leaf = natural(*component, "leaf"),
             role = natural(*component, "role"),
             native = natural(*component, "native");
        auto facet = text(*component, "facet");
        const auto &actual = reconstructed[i];
        if (!path || !leaf || !role || !native || !facet ||
            !charge(path->size() + 1) || path->size() != actual.path.size() ||
            *leaf != actual.leaf || *role != actual.role ||
            *native != actual.native ||
            *facet != componentFacetName(actual.facet))
          return fail("port component identity, order or selection differs");
        for (unsigned j = 0; j < path->size(); ++j)
          if ((*path)[j].getAsInteger() != int64_t(actual.path[j]))
            return fail("port component path differs");
      }
      port.components = std::move(reconstructed);
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
    if (!remaining)
      return error("source.limit", "schema identity budget exceeded");
    --remaining;
    FramedHash hash(remaining);
    hash.frame("zkc.language.schema/0");
    hash.frame(typeKindName(schema.kind));
    hash.frame(schema.identity);
    if (!schema.generated.empty())
      hash.frame(schema.generated);
    hash.frame(std::to_string(schema.custody));
    hash.frame(schema.sealed ? "1" : "0");
    hash.frame(schema.constructible ? "1" : "0");
    for (bool allowed : {schema.permissions.copy, schema.permissions.drop})
      hash.frame(allowed ? "1" : "0");
    hash.frame(std::to_string(schema.roles.size()));
    for (const auto &role : schema.roles)
      hash.frame(role);
    if (schema.element) {
      hash.frame("element");
      auto element = schemaIdentity(*schema.element);
      if (!element)
        return element.takeError();
      hash.frame(*element);
    } else
      hash.frame("");
    if (schema.oracleData) {
      hash.frame("data_schema");
      auto data = schemaIdentity(*schema.oracleData);
      if (!data)
        return data.takeError();
      hash.frame(*data);
    } else
      hash.frame("");
    if (logicalSchema(schema)) {
      std::vector<PortLeaf> leaves;
      unsigned count = 0;
      if (!observe(schema, {}, leaves, count)) {
        if (failure)
          return std::move(failure);
        return error("source.interface", "invalid logical schema identity");
      }
      hash.frame(std::to_string(leaves.size()));
      for (const auto &leaf : leaves) {
        if (!leaf.schema->oracle) {
          hash.frame(leaf.data);
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
    std::function<Error(const ValuePlacement &, unsigned)> formula =
        [&](const ValuePlacement &p, unsigned level) -> Error {
      if (!remaining || level > limits.typeDepth)
        return error("source.limit", "schema formula identity budget exceeded");
      --remaining;
      if (const auto *data = std::get_if<DataPlacement>(&p.value)) {
        hash.frame("data");
        hash.frame(std::to_string(data->roles.size()));
        for (unsigned role : data->roles)
          hash.frame(std::to_string(role));
      } else if (const auto *oracle = std::get_if<OraclePlacement>(&p.value)) {
        hash.frame("oracle");
        hash.frame(std::to_string(oracle->holder));
        hash.frame(std::to_string(oracle->receivers.size()));
        for (unsigned role : oracle->receivers)
          hash.frame(std::to_string(role));
      } else {
        const auto &product = std::get<ProductPlacement>(p.value);
        hash.frame("product");
        hash.frame(product.instance);
        hash.frame(std::to_string(product.arguments.size()));
        for (unsigned role : product.arguments)
          hash.frame(std::to_string(role));
        hash.frame(std::to_string(product.fields.size()));
        for (const auto &field : product.fields)
          if (auto e = formula(field, level + 1))
            return e;
      }
      return Error::success();
    };
    auto fields = [&](ArrayRef<InterfaceField> fields) -> Error {
      hash.frame(std::to_string(fields.size()));
      for (const auto &field : fields) {
        if (!remaining)
          return error("source.limit", "schema field identity budget exceeded");
        --remaining;
        hash.frame(field.name);
        hash.frame(std::to_string(field.offset));
        hash.frame(field.isPublic ? "1" : "0");
        hash.frame(field.placement ? "placement" : "");
        if (field.placement)
          if (auto e = formula(*field.placement, 0))
            return e;
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
  std::shared_ptr<const InterfaceSchema>
  project(const InterfacePort &port, const json::Array &path,
          std::vector<unsigned> &indices, std::vector<unsigned> &native,
          bool anchor = false, std::optional<unsigned> role = {},
          bool publicOnly = false, unsigned *holder = nullptr,
          bool specification = false, bool association = false) {
    auto selected = port.schema;
    for (const auto &item : path) {
      if (!charge(1))
        return {};
      auto at = item.getAsInteger();
      if (!at || *at < 0 || uint64_t(*at) >= selected->fields.size() ||
          (selected->custody && !specification) ||
          selected->kind == Type::Kind::Variant ||
          selected->kind == Type::Kind::Associated ||
          (publicOnly && !selected->fields[*at].isPublic)) {
        fail("selector path is not an accessible product projection");
        return {};
      }
      indices.push_back(unsigned(*at));
      selected = selected->fields[*at].schema;
    }
    if (anchor &&
        (selected->kind != Type::Kind::Oracle || !selected->oracleData)) {
      fail("anchor selector requires one singleton oracle field");
      return {};
    }
    if (!anchor && !association && logicalSchema(*selected)) {
      fail("logical selection requires a singleton anchor");
      return {};
    }
    std::set<unsigned> seen;
    unsigned available = 0;
    for (const auto &component : port.components) {
      if (!charge(component.path.size() + 1))
        return {};
      if (component.path.size() < indices.size() ||
          !llvm::equal(ArrayRef(component.path).take_front(indices.size()),
                       indices))
        continue;
      if (anchor) {
        if (component.path != indices)
          continue;
        if (component.facet == InterfaceComponentFacet::OracleData && holder)
          *holder = component.role;
        if (component.facet != InterfaceComponentFacet::OracleAnchor)
          continue;
      } else {
        if (component.facet != InterfaceComponentFacet::Data)
          continue;
        if (role && component.role != *role)
          continue;
      }
      if (seen.insert(component.native).second)
        native.push_back(component.native);
      ++available;
    }
    if ((!association &&
         native.size() != (anchor ? 1 : selected->leaves.size())) ||
        (role && !selected->leaves.empty() && !available)) {
      fail("selector participant does not have every selected component");
      return {};
    }
    // Zero-width ordinary selections retain their placement availability.
    if (role && selected->leaves.empty()) {
      const ValuePlacement *placed =
          port.placement ? &*port.placement : nullptr;
      auto current = port.schema;
      for (auto index : indices) {
        if (placed)
          if (auto *product = std::get_if<ProductPlacement>(&placed->value))
            placed =
                &product
                     ->fields[current->kind == Type::Kind::Array ? 0 : index];
        current = current->fields[index].schema;
      }
      std::function<bool(const ValuePlacement &, unsigned)> available =
          [&](const ValuePlacement &where, unsigned depth) {
            if (!charge(1) || depth > limits.typeDepth)
              return false;
            if (const auto *data = std::get_if<DataPlacement>(&where.value))
              return charge(data->roles.size()) &&
                     is_contained(data->roles, *role);
            if (const auto *product =
                    std::get_if<ProductPlacement>(&where.value))
              return !product->fields.empty() &&
                     llvm::all_of(product->fields, [&](const auto &field) {
                       return available(field, depth + 1);
                     });
            return false;
          };
      if (!placed || !available(*placed, 0)) {
        fail("zero-width selection is unavailable at this role");
        return {};
      }
    }
    return anchor ? selected->oracleData : selected;
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
      if (found == roleIndices.end())
        return fail("selector does not name an actual participant component"),
               std::nullopt;
      owner = found->second;
    }
    InterfaceSelector result{
        *direction == "output", *port, owner, {}, {}, anchor};
    auto schema = project(ports[*port], *path, result.path, result.native,
                          anchor, anchor ? std::nullopt : std::optional(owner),
                          false, &result.role, true);
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
      // A logical handle's head is the name a frontend constructor row spells.
      const auto *head =
          *tag == "builtin" ? protocol::frontendConstructor(name) : nullptr;
      result.kind = *tag == "formal"         ? K::Formal
                    : name == "oracle.table" ? K::OracleKind
                    : head                   ? logicalHeadKind(head->form)
                                             : K::Builtin;
      result.domain = name == "oracle.table" ? "table" : head ? "" : name.str();
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
  /// SHA-256 of the canonical key over the carrier's authority rows. A path
  /// without a row has no identity.
  std::optional<std::string> canonicalIdentity(const Type &type) {
    auto key = canonicalTypeKey(
        type, [&](StringRef path) -> Expected<std::optional<std::string>> {
          auto found = retainedAuthorities.find(path.str());
          if (found == retainedAuthorities.end())
            return error("source.interface",
                         "retained nominal path has no authority row");
          return found->second;
        });
    if (!key) {
      consumeError(key.takeError());
      return fail("retained nominal path has no authority row"), std::nullopt;
    }
    if (!charge(key->size()))
      return {};
    return toHex(SHA256::hash(arrayRefFromStringRef(*key)), true);
  }
  std::optional<std::string> retainedIdentity(const json::Value &value) {
    auto type = retainedType(value);
    if (!type)
      return {};
    return canonicalIdentity(*type);
  }
  bool retainedSchemaType(const Type &type, const InterfaceSchema &schema,
                          unsigned depth = 0) {
    if (depth > limits.typeDepth || !charge(1)) {
      if (!failure)
        failure = error("source.limit", "retained schema type depth exceeded");
      return false;
    }
    auto identity = canonicalIdentity(type);
    if (!identity || !charge(1))
      return false;
    if (schema.kind != type.kind || *identity != schema.identity ||
        schema.type != spelling(type))
      return fail("retained field static type differs from complete schema");
    if (type.kind == Type::Kind::Array) {
      if (type.arguments.size() != 1 || !type.dimension.isClosed() ||
          !schema.element ||
          schema.fields.size() != type.dimension.closedValue() ||
          !retainedSchemaType(type.arguments[0], *schema.element, depth + 1))
        return fail("retained array element or extent differs");
    } else if (type.kind == Type::Kind::Tuple) {
      if (type.arguments.size() != schema.fields.size())
        return fail("retained tuple arity differs");
      for (unsigned i = 0; i < type.arguments.size(); ++i)
        if (!retainedSchemaType(type.arguments[i], *schema.fields[i].schema,
                                depth + 1))
          return false;
    }
    return true;
  }
  bool retainedSchemas(protocol_ir::ProtocolModuleOp module) {
    bool logical = llvm::any_of(schemas, [](const auto &item) {
      return item.second->kind == Type::Kind::LogicalRecord;
    });
    if (!logical && !module->hasAttr("source_declarations"))
      return true;
    auto declarations =
        exportDeclarationData(module->getAttr("source_declarations"));
    if (!declarations) {
      consumeError(declarations.takeError());
      return fail("logical record declaration carrier is absent");
    }
    auto *tables = declarations->getAsArray();
    if (!tables || tables->size() != 3 || !(*tables)[0].getAsArray() ||
        !(*tables)[2].getAsArray())
      return fail("logical declaration tables differ");
    // Authority rows are sorted by path; a revision is SHA-256 hex and null
    // marks a generated declaration.
    retainedAuthorities.clear();
    for (const auto &value : *(*tables)[2].getAsArray()) {
      auto *row = value.getAsArray();
      auto path =
          row && row->size() == 2 ? (*row)[0].getAsString() : std::nullopt;
      auto revision = path ? (*row)[1].getAsString() : std::nullopt;
      if (!path || !charge(path->size() + 66) ||
          ((*row)[1].kind() != json::Value::Null &&
           (!revision || !hash(*revision))) ||
          (!retainedAuthorities.empty() &&
           retainedAuthorities.rbegin()->first >= *path))
        return fail("retained authority rows differ");
      retainedAuthorities.emplace(
          path->str(), revision ? std::optional<std::string>(revision->str())
                                : std::nullopt);
    }
    std::map<std::string, const json::Array *> records;
    // Nominal rows retain [type, resource, sealed, members, roles, slot].
    // Product members are [name, type, placement]; variant members are
    // [alternative, product members]. Native payload widths cannot
    // authenticate omitted zero-leaf members.
    for (const auto &value : *(*tables)[0].getAsArray()) {
      auto *record = value.getAsArray();
      if (!record || record->size() != 6 || !(*record)[1].getAsString() ||
          !(*record)[2].getAsBoolean() || !(*record)[3].getAsArray() ||
          !(*record)[4].getAsArray())
        return fail("retained record shape differs");
      auto identity = retainedIdentity((*record)[0]);
      if (!identity || !records.emplace(*identity, record).second)
        return fail("retained record identity differs or repeats");
    }
    std::set<const InterfaceSchema *> checked;
    // A retained formula names roles of its row's telescope; the schema field
    // places the same tree by ordinal. Product instances are schema digests
    // there and absent here; the tree shape and role order must agree.
    std::function<bool(const json::Value &, const ValuePlacement &,
                       ArrayRef<std::string>, unsigned)>
        samePlacement = [&](const json::Value &value,
                            const ValuePlacement &expected,
                            ArrayRef<std::string> telescope, unsigned depth) {
          auto *node = value.getAsArray();
          if (depth > limits.typeDepth || !charge(1) || !node || node->empty())
            return false;
          auto ordinal =
              [&](const json::Value &role) -> std::optional<unsigned> {
            auto name = role.getAsString();
            auto found = name ? llvm::find(telescope, *name) : telescope.end();
            if (found == telescope.end())
              return std::nullopt;
            return unsigned(found - telescope.begin());
          };
          auto ordinals = [&](const json::Value &roles,
                              ArrayRef<unsigned> actual) {
            auto *list = roles.getAsArray();
            if (!list || list->size() != actual.size())
              return false;
            for (unsigned i = 0; i < actual.size(); ++i)
              if (ordinal((*list)[i]) != actual[i])
                return false;
            return true;
          };
          if (const auto *data = std::get_if<DataPlacement>(&expected.value))
            return node->size() == 2 && (*node)[0] == json::Value("data") &&
                   ordinals((*node)[1], data->roles);
          if (const auto *oracle =
                  std::get_if<OraclePlacement>(&expected.value))
            return node->size() == 3 && (*node)[0] == json::Value("oracle") &&
                   ordinal((*node)[1]) == oracle->holder &&
                   ordinals((*node)[2], oracle->receivers);
          const auto &product = std::get<ProductPlacement>(expected.value);
          auto *fields = node->size() == 3 ? (*node)[2].getAsArray() : nullptr;
          if ((*node)[0] != json::Value("product") ||
              !ordinals((*node)[1], product.arguments) || !fields ||
              fields->size() != product.fields.size())
            return false;
          for (unsigned i = 0; i < fields->size(); ++i)
            if (!samePlacement((*fields)[i], product.fields[i], telescope,
                               depth + 1))
              return false;
          return true;
        };
    auto matchFields = [&](const json::Array &fields,
                           ArrayRef<InterfaceField> expected,
                           ArrayRef<std::string> telescope) {
      if (!charge(1 + fields.size()) || fields.size() != expected.size())
        return fail("nominal schema omits private or zero-leaf fields");
      for (unsigned i = 0; i < fields.size(); ++i) {
        auto *field = fields[i].getAsArray();
        if (!field || field->size() != 3 ||
            (*field)[0].getAsString() != expected[i].name)
          return fail("retained nominal field name or order differs");
        auto type = retainedType((*field)[1]);
        if (!type || !retainedSchemaType(*type, *expected[i].schema))
          return fail("retained nominal field type differs");
        const auto &placement = (*field)[2];
        if ((placement.kind() == json::Value::Null) != !expected[i].placement ||
            (expected[i].placement &&
             !samePlacement(placement, *expected[i].placement, telescope, 0)))
          return fail("retained member placement differs from schema");
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
            // Only a generated declaration has no authored or installed
            // authority.
            auto authority = retainedAuthorities.find(type->domain);
            if (authority == retainedAuthorities.end() ||
                authority->second.has_value() != schema.generated.empty())
              return fail("retained authority differs from schema generation");
            if (record[2].getAsBoolean() != schema.sealed)
              return fail("retained sealing policy differs from schema");
            // The row's telescope is the schema's role telescope, and its
            // custody slot names the schema's resource units.
            std::vector<std::string> telescope;
            for (const auto &role : *record[4].getAsArray()) {
              auto name = role.getAsString();
              if (!name || !charge(name->size() + 1))
                return fail("retained role telescope differs from schema");
              telescope.push_back(name->str());
            }
            if (telescope != schema.roles)
              return fail("retained role telescope differs from schema");
            auto slot = record[5].getAsString();
            if (schema.custody
                    ? !slot || *slot != "zkl_resource_" + schema.identity
                    : record[5].kind() != json::Value::Null)
              return fail("retained custody slot differs from schema");
            auto resource = record[1].getAsString();
            if (!resource ||
                (resource != "ordinary" && resource != "linear" &&
                 resource != "affine") ||
                (resource == "linear" &&
                 (schema.permissions.copy || schema.permissions.drop)) ||
                (resource == "affine" && schema.permissions.copy) ||
                (resource == "ordinary" && schema.custody) ||
                (resource != "ordinary" &&
                 (schema.constructible ||
                  schema.custody != (schema.kind == Type::Kind::LogicalRecord
                                         ? schema.roles.size()
                                         : 1))))
              return fail("retained resource policy differs from schema");
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
                                 schema.alternatives[i].fields, telescope))
                  return fail("retained variant fields or order differ");
              }
            } else if (!matchFields(members, schema.fields, telescope))
              return false;
          }
          if (schema.element && !bind(*schema.element))
            return false;
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
      if ((item.second->kind == Type::Kind::LogicalRecord ||
           item.second->kind == Type::Kind::Record ||
           item.second->kind == Type::Kind::Variant) &&
          !bind(*item.second))
        return false;
    return true;
  }
  bool transportAttributes(mlir::Operation &operation, const PortLeaf &leaf,
                           ArrayRef<unsigned> mapping,
                           std::optional<uint64_t> maximum, bool binding) {
    const auto *oracle =
        leaf.placement ? std::get_if<OraclePlacement>(&leaf.placement->value)
                       : nullptr;
    if (!oracle)
      return fail("logical transport has no oriented family");
    auto mapped = [&](unsigned role) {
      return mapping.empty() ? role : mapping[role];
    };
    auto holder = operation.getAttrOfType<mlir::StringAttr>("holder");
    std::vector<unsigned> receivers;
    for (auto role : oracle->receivers)
      receivers.push_back(mapped(role));
    llvm::sort(receivers);
    if (!holder ||
        holder.getValue() != nativeRoleName(mapped(oracle->holder)) ||
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
                   leaves, count, 0,
                   port.placement ? &*port.placement : nullptr))
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
            !transportAttributes(*binding, leaf, mapping, leaf.maximumRows,
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
                   leaves, count, 0,
                   port.placement ? &*port.placement : nullptr))
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
            !transportAttributes(*parts, leaf, mapping, {}, false))
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
            if (!charge(protocol.roles.size() + 1)) {
              valid = false;
              return;
            }
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
    auto *obj =
        object(value, {"symbol", "roles", "inputs", "outputs", "services",
                       "clauses", "common_input_requirements"});
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
    if (rs->empty())
      return fail("empty role roster");
    if (rs->size() > protocol::instances::protocolRoleLimit)
      return fail("role roster exceeds the protocol.roles limit");
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
    auto common = decodeCommonRequirements(
        *obj->get("common_input_requirements"), *current, remaining, limits);
    if (!common) {
      failure = common.takeError();
      return false;
    }
    current->commonInputRequirements = std::move(*common);
    if (auto e = checkNativeCommonRequirements(function, *current, remaining,
                                               limits)) {
      failure = std::move(e);
      return false;
    }
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
    std::vector<unsigned> publicNative;
    if (view.proof) {
      auto selected = detail::interfacePublicNative(
          protocol, view.proof->publicInputs, view.proof->verifier, remaining,
          limits);
      if (!selected) {
        failure = selected.takeError();
        return false;
      }
      publicNative = std::move(*selected);
    }
    std::set<unsigned> expected;
    std::set<unsigned> verifierKeys, covered;
    std::map<unsigned, std::set<unsigned>> dataRoles;
    for (const auto &input : protocol.inputs) {
      for (const auto &component : input.components) {
        if (!charge(component.path.size() + 1))
          return false;
        if (component.facet == InterfaceComponentFacet::Data)
          dataRoles[component.native].insert(component.role);
      }
      std::vector<PortLeaf> leaves;
      unsigned width = 0;
      if (!observe(*input.schema,
                   input.oracle ? input.oracle->maximumRows : std::nullopt,
                   leaves, width, 0, &*input.placement))
        return false;
      for (const auto &leaf : leaves) {
        if (leaf.schema->oracle || leaf.custody)
          continue;
        auto policy = leafPermissions(leaf.data);
        if (!policy)
          return false;
        const auto &native = nativeLeaves.at(leaf.data);
        unsigned index = input.native[leaf.offset];
        if (view.proof && native.proverKey &&
            dataRoles[index].count(view.proof->verifier))
          return fail("proof prover keys must stay with the prover");
        if (native.setup)
          expected.insert(index);
        if (native.verifierKey) {
          if (leaf.schema->kind != Type::Kind::Builtin ||
              leaf.schema->leaves.size() != 1)
            return fail("key initialization requires a whole builtin field");
          verifierKeys.insert(index);
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
                     selected.native, false, {}, true, nullptr, false, true))
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
            if (!is_contained(publicNative, index) ||
                !dataRoles[index].count(view.proof->verifier))
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
                       "completion", "target", "construction", "gates"});
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
    auto *gates = array(*obj, "gates");
    if (!gates || gates->size() > 64)
      return fail("invalid proof gate count");
    std::set<std::vector<std::string>> selectedGates;
    for (const auto &item : *gates) {
      auto *gate = object(item, {"path", "bits"});
      auto *path = gate ? array(*gate, "path") : nullptr;
      auto bits = gate ? gate->getInteger("bits") : std::nullopt;
      if (!path || path->empty() || path->size() > 64 || !bits || *bits < 0 ||
          *bits > 64)
        return fail("invalid proof gate selector");
      ProofGate selected;
      selected.bits = unsigned(*bits);
      size_t bytes = 0;
      for (const auto &component : *path) {
        auto part = component.getAsString();
        if (!part || !charge(part->size() + 1) || !isSourceIdentifier(*part) ||
            (bytes += part->size() + 1) > 4096)
          return fail("invalid proof gate path");
        selected.path.push_back(part->str());
      }
      if (!selectedGates.insert(selected.path).second)
        return fail("duplicate proof gate selector");
      proof.gates.push_back(std::move(selected));
    }
    for (const auto &input : *publicInputs) {
      if (!charge(1))
        return false;
      const auto *selected = object(input, {"port", "path", "role"});
      if (!selected)
        return false;
      auto port = natural(*selected, "port");
      auto role = text(*selected, "role", limits.identifierBytes);
      auto *path = array(*selected, "path");
      if (!port || !role || !path || *port >= current->inputs.size() ||
          *role != *verifier || path->size() > limits.typeDepth)
        return fail("invalid public field selection");
      EntryInputSelection result{*port, {}, proof.verifier, {}};
      for (const auto &step : *path) {
        if (!charge(1))
          return false;
        auto index = step.getAsInteger();
        if (!index || *index < 0 || uint64_t(*index) > UINT32_MAX)
          return fail("invalid public path ordinal");
        result.path.push_back(*index);
      }
      proof.publicInputs.push_back(std::move(result));
    }
    auto publicNative = detail::interfacePublicNative(
        *current, proof.publicInputs, proof.verifier, remaining, limits);
    if (!publicNative) {
      failure = publicNative.takeError();
      return false;
    }
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
    if (!proof.gates.empty() &&
        (proof.construction != ProofEntry::Construction::FiatShamir ||
         !proof.selectedConstruction.empty() ||
         !protocol::installedDomains().hasFact("IndexBlockTranscript",
                                               {proof.suite})))
      return fail("gates require a direct native block construction");
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
        bool visible = operand.anchor
                           ? operand.role == proof.verifier
                           : llvm::all_of(operand.native, [&](unsigned index) {
                               return llvm::any_of(
                                   port.components, [&](const auto &component) {
                                     return component.native == index &&
                                            component.role == proof.verifier &&
                                            component.facet ==
                                                InterfaceComponentFacet::Data;
                                   });
                             });
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
    auto result = schema(value, 0, leaves);
    if (result && logicalSchema(*result)) {
      fail("Host schema contains logical category");
      return {};
    }
    return result;
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
  Expected<std::string> runIdentity(const json::Value &value) {
    auto *object = value.getAsObject();
    auto *leaves = object ? object->getArray("leaves") : nullptr;
    if (!leaves)
      return error("source.interface", "schema leaves missing");
    std::vector<std::string> expected;
    for (const auto &leaf : *leaves) {
      auto text = leaf.getAsString();
      if (!text || !charge(text->size() + 1)) {
        if (!failure)
          fail("invalid schema leaf");
        return std::move(failure);
      }
      expected.push_back(text->str());
    }
    auto result = schema(value, 0, expected);
    if (!result)
      return std::move(failure);
    return schemaIdentity(*result);
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
Expected<std::string> interfaceSchemaIdentity(const json::Value &value,
                                              const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  return Reader(limits, {}).runIdentity(value);
}
Expected<LanguageInterface> decodeInterface(mlir::ModuleOp module,
                                            StringRef digest,
                                            const json::Value &value,
                                            const Limits &limits,
                                            ArrayRef<Asset> assets) {
  return Reader(limits, assets).run(value, module, digest);
}
} // namespace zkc::language::detail
