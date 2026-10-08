#include "LanguageInterface.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
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
  std::map<std::string, std::shared_ptr<const InterfaceSchema>> schemas;
  StringMap<unsigned> roleIndices;
  std::map<std::string, std::string> nominalLabels;
  std::map<std::string, Permissions> nativePermissions;
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
      if (!name || name.getValue() != view.roles[roles[i]])
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
    auto found = nativePermissions.find(spelling.str());
    if (found != nativePermissions.end())
      return found->second;
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
    nativePermissions.emplace(spelling.str(), result);
    return result;
  }
  bool nominal(StringRef identity, StringRef label) {
    if (!charge(identity.size() + label.size() + 1))
      return false;
    auto [found, inserted] = nominalLabels.emplace(identity.str(), label.str());
    return inserted || found->second == label ||
           fail("one native nominal identity has conflicting source labels");
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
        a.custody != b.custody || !(a.permissions == b.permissions) ||
        a.leaves != b.leaves ||
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
  std::shared_ptr<const InterfaceSchema>
  schema(const json::Value &value, unsigned depth,
         ArrayRef<std::string> expected) {
    if (depth > limits.typeDepth) {
      failure = error("source.limit", "interface schema depth exceeded");
      return {};
    }
    if (!charge(1))
      return {};
    auto *obj = object(value, {"type", "custody", "permissions", "fields",
                               "alternatives", "leaves"});
    if (!obj)
      return {};
    auto type = text(*obj, "type");
    auto custody = obj->getBoolean("custody");
    auto *perms = array(*obj, "permissions"), *fs = array(*obj, "fields"),
         *alts = array(*obj, "alternatives"), *ls = array(*obj, "leaves");
    if (!type || !perms || !fs || !alts || !ls)
      return {};
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
         !hash(StringRef(result->leaves.front())
                   .drop_front(custodyPrefix.size())))) {
      fail("invalid nominal custody prefix");
      return {};
    }
    if (start && !nominal(result->leaves.front(), result->type))
      return {};
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
      auto *identity = descriptor->nominal.getAsArray();
      if (!identity || identity->size() != 2 ||
          (*identity)[0].getAsString() != "zkc.language" ||
          !(*identity)[1].getAsString() ||
          (*identity)[1].getAsString()->empty() ||
          !nominal("variant:" + (*identity)[1].getAsString()->str(),
                   result->type)) {
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
    auto [found, inserted] = schemas.emplace(result->type, result);
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
  bool read(const json::Value &value, mlir::ModuleOp module, StringRef digest) {
    auto *obj =
        object(value, {"format", "capture", "original", "toolchain", "entry",
                       "protocol", "roles", "inputs", "outputs", "services"});
    if (!obj)
      return false;
    auto format = text(*obj, "format");
    auto capture = text(*obj, "capture"), original = text(*obj, "original"),
         toolchain = text(*obj, "toolchain"),
         entry = text(*obj, "entry",
                      limits.moduleBytes + 2 + limits.identifierBytes),
         symbol = text(*obj, "protocol", limits.symbolBytes);
    auto *rs = array(*obj, "roles"), *ins = array(*obj, "inputs"),
         *outs = array(*obj, "outputs"), *services = array(*obj, "services");
    if (!format || !capture || !original || !toolchain || !entry || !symbol ||
        !rs || !ins || !outs || !services)
      return false;
    if (*format != "zkc.language-interface/2" || !hash(*capture) ||
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
    view.protocol = symbol->str();
    std::set<std::string> usedRoles;
    if (rs->empty() || rs->size() > 1024)
      return fail("invalid role roster size");
    for (const auto &item : *rs) {
      auto name = item.getAsString();
      if (!name || name->size() > limits.identifierBytes ||
          !identifier(*name) || !usedRoles.insert(name->str()).second)
        return fail("invalid or duplicate role");
      roleIndices.try_emplace(*name, view.roles.size());
      view.roles.push_back(name->str());
    }
    if (!module || !module->getAttrs().empty() ||
        !hasSingleElement(*module.getBody()))
      return fail("expected one unadorned protocol module");
    auto native = mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(
        module.getBody()->front());
    if (!native || native.getProfile() != protocol_ir::Profile::Protocol ||
        !hasSingleElement(native.getBody()))
      return fail("expected mathematical protocol profile");
    protocol_ir::MathematicalOp function;
    for (auto &op : native.getBody().front()) {
      if (!charge(1))
        return false;
      auto candidate = mlir::dyn_cast<protocol_ir::MathematicalOp>(op);
      if (candidate && candidate.getSymName() == *symbol)
        function = candidate;
    }
    if (!function || function.getRoles().size() != view.roles.size())
      return fail("protocol symbol or role roster differs");
    std::vector<unsigned> roster;
    for (unsigned i = 0; i < view.roles.size(); ++i)
      roster.push_back(i);
    if (!matchesRoles(function.getRoles(), roster))
      return false;
    auto type = function.getFunctionType();
    unsigned input = 0, output = 0;
    if (!ports(*ins, type.getInputs(), function.getInputRoles(), view.inputs,
               input) ||
        !ports(*outs, type.getResults(), function.getOutputRoles(),
               view.outputs, output))
      return false;
    std::set<std::string> names;
    for (const auto &port : view.inputs)
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
      view.services.push_back({name->str(), contract->str(), role, input++});
    }
    return (input == type.getNumInputs() && output == type.getNumResults()) ||
           fail("interface omits native ports");
  }

public:
  explicit Reader(const Limits &limits)
      : limits(limits), remaining(limits.work) {
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
Expected<LanguageInterface> readInterface(mlir::ModuleOp module,
                                          StringRef digest, StringRef bytes,
                                          const Limits &limits) {
  auto value = parseInterface(bytes, limits);
  if (!value)
    return value.takeError();
  return decodeInterface(module, digest, *value, limits);
}
Expected<LanguageInterface> decodeInterface(mlir::ModuleOp module,
                                            StringRef digest,
                                            const json::Value &value,
                                            const Limits &limits) {
  return Reader(limits).run(value, module, digest);
}
} // namespace zkc::language::detail
