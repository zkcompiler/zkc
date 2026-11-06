#include "ComponentContracts.h"
#include "SourceView.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include <functional>
#include <iterator>
#include <map>
#include <set>
#include <variant>
using namespace llvm;
namespace zkc::language {
namespace {
// Borrow either actual native declaration attributes or the explicit wire
// tree. Native indexing never materializes JSON, even for declaration keys.
class DeclarationArray;
class DeclarationValue {
  mlir::Attribute attribute;
  const json::Value *wire = nullptr;
  const char *literal = nullptr;

public:
  DeclarationValue(mlir::Attribute value) : attribute(value) {}
  DeclarationValue(const json::Value &value) : wire(&value) {}
  DeclarationValue(const char *value) : literal(value) {}
  std::optional<DeclarationArray> getAsArray() const;
  std::optional<StringRef> getAsString() const {
    if (wire)
      return wire->getAsString();
    if (literal)
      return StringRef(literal);
    if (auto text = mlir::dyn_cast_or_null<mlir::StringAttr>(attribute))
      return text.getValue();
    return std::nullopt;
  }
  std::optional<bool> getAsBoolean() const {
    if (wire)
      return wire->getAsBoolean();
    if (auto flag = mlir::dyn_cast_or_null<mlir::BoolAttr>(attribute))
      return flag.getValue();
    return std::nullopt;
  }
  std::optional<uint64_t> getAsUINT64() const {
    if (wire)
      return wire->getAsUINT64();
    auto value = mlir::dyn_cast_or_null<mlir::IntegerAttr>(attribute);
    if (value && value.getType().isUnsignedInteger(64))
      return value.getValue().getZExtValue();
    return std::nullopt;
  }
  bool isNull() const {
    return wire ? wire->kind() == json::Value::Null
                : mlir::isa_and_nonnull<mlir::UnitAttr>(attribute);
  }
  bool operator==(const DeclarationValue &other) const {
    auto lhs = getAsString(), rhs = other.getAsString();
    return lhs && rhs && *lhs == *rhs;
  }
  bool operator!=(const DeclarationValue &other) const {
    return !(*this == other);
  }
  using Key = std::variant<uintptr_t, std::string>;
  Expected<Key> key(uint64_t &remaining) const;
  bool belongsTo(mlir::MLIRContext *context) const {
    return !attribute || attribute.getContext() == context;
  }
  const json::Value *jsonValue() const { return wire; }
};
class DeclarationArray {
  mlir::ArrayAttr attribute;
  const json::Array *wire = nullptr;

public:
  DeclarationArray(mlir::ArrayAttr value) : attribute(value) {}
  DeclarationArray(const json::Array &value) : wire(&value) {}
  size_t size() const { return wire ? wire->size() : attribute.size(); }
  bool empty() const { return size() == 0; }
  DeclarationValue operator[](size_t i) const {
    return wire ? DeclarationValue((*wire)[i]) : DeclarationValue(attribute[i]);
  }
  struct Iterator {
    using value_type = DeclarationValue;
    using reference = DeclarationValue;
    using pointer = void;
    using difference_type = ptrdiff_t;
    using iterator_category = std::forward_iterator_tag;
    const DeclarationArray *array;
    size_t index;
    DeclarationValue operator*() const { return (*array)[index]; }
    Iterator &operator++() {
      ++index;
      return *this;
    }
    bool operator!=(const Iterator &other) const {
      return index != other.index;
    }
    bool operator==(const Iterator &other) const {
      return index == other.index;
    }
  };
  Iterator begin() const { return {this, 0}; }
  Iterator end() const { return {this, size()}; }
};
std::optional<DeclarationArray> DeclarationValue::getAsArray() const {
  if (wire) {
    auto *array = wire->getAsArray();
    return array ? std::optional(DeclarationArray(*array)) : std::nullopt;
  }
  auto array = mlir::dyn_cast_or_null<mlir::ArrayAttr>(attribute);
  return array ? std::optional(DeclarationArray(array)) : std::nullopt;
}
using J = DeclarationValue;
using A = DeclarationArray;
A array(const J &value) { return *value.getAsArray(); }
StringRef string(const J &value) { return *value.getAsString(); }
Expected<DeclarationValue::Key>
DeclarationValue::key(uint64_t &remaining) const {
  if (wire)
    return Key(printJson(*wire));
  auto normalized = canonicalDeclarationTerm(attribute, remaining);
  if (!normalized)
    return normalized.takeError();
  return Key(reinterpret_cast<uintptr_t>(normalized->getAsOpaquePointer()));
}
} // namespace
Expected<mlir::Attribute> canonicalDeclarationTerm(mlir::Attribute attribute,
                                                   uint64_t &remaining) {
  // Static terms contain arrays, strings and null. A StringAttr's optional type
  // is not part of the declaration semantics. Intern the normalized native tree
  // so keys agree with textual equality without a publication round trip.
  std::function<mlir::Attribute(mlir::Attribute, unsigned)> canonical =
      [&](mlir::Attribute value, unsigned depth) -> mlir::Attribute {
    if (!remaining || depth >= 128)
      return {};
    --remaining;
    if (mlir::isa_and_nonnull<mlir::UnitAttr>(value))
      return value;
    if (auto text = mlir::dyn_cast<mlir::StringAttr>(value)) {
      if (text.getValue().size() > remaining)
        return {};
      remaining -= text.getValue().size();
      return mlir::StringAttr::get(value.getContext(), text.getValue());
    }
    auto array = mlir::dyn_cast<mlir::ArrayAttr>(value);
    if (!array || array.size() > remaining)
      return {};
    SmallVector<mlir::Attribute> children;
    for (auto child : array) {
      auto normalized = canonical(child, depth + 1);
      if (!normalized)
        return {};
      children.push_back(normalized);
    }
    return mlir::ArrayAttr::get(value.getContext(), children);
  };
  auto normalized = canonical(attribute, 0);
  if (!normalized)
    return error("component-declaration-limit");
  return normalized;
}
namespace {

// The semantic static-term grammar has no table, text or arity ceiling. Its
// native caller has already charged all retained metadata, and recursive work
// shares the subject allowance. The public wire checker keeps its own limits.
enum class StaticTermCategory { Term, Descriptor, Natural };
bool nativeStaticTerm(const J &value, uint64_t &remaining, unsigned depth = 0,
                      StaticTermCategory category = StaticTermCategory::Term) {
  if (!remaining || depth >= 64)
    return false;
  --remaining;
  auto node = value.getAsArray();
  if (!node || node->empty())
    return false;
  auto tag = (*node)[0].getAsString();
  if (!tag)
    return false;
  if (category == StaticTermCategory::Natural && *tag != "nat")
    return false;
  if (category == StaticTermCategory::Descriptor &&
      *tag != "descriptor-product" && *tag != "descriptor-sequence" &&
      *tag != "builtin")
    return false;
  auto text = [](const J &value) {
    auto s = value.getAsString();
    return s && !s->empty() && json::isUTF8(*s) && !s->contains('\0');
  };
  auto decimal = [&](const J &value) {
    auto s = value.getAsString();
    return text(value) && (s->size() == 1 || s->front() != '0') &&
           all_of(*s, [](char c) { return c >= '0' && c <= '9'; });
  };
  auto arguments = [&](unsigned index, StaticTermCategory childrenCategory =
                                           StaticTermCategory::Term) {
    auto children = (*node)[index].getAsArray();
    if (!children || children->size() > remaining)
      return false;
    for (const auto &child : *children)
      if (!nativeStaticTerm(child, remaining, depth + 1, childrenCategory))
        return false;
    return true;
  };
  if (*tag == "descriptor-product")
    return node->size() == 2 && arguments(1, StaticTermCategory::Descriptor);
  if (*tag == "descriptor-sequence")
    return node->size() == 3 &&
           nativeStaticTerm((*node)[1], remaining, depth + 1,
                            StaticTermCategory::Descriptor) &&
           ((*node)[2].isNull() ||
            nativeStaticTerm((*node)[2], remaining, depth + 1,
                             StaticTermCategory::Natural));
  if (category == StaticTermCategory::Descriptor)
    return node->size() == 3 && (*node)[1].getAsString() == "finite" &&
           (*node)[2].getAsArray() && (*node)[2].getAsArray()->size() == 1 &&
           arguments(2);
  if (*tag == "nat")
    return node->size() == 2 && decimal((*node)[1]);
  if (*tag == "field" || *tag == "group")
    return node->size() == 2 && text((*node)[1]);
  if (*tag == "domain" || *tag == "asset")
    return node->size() == 3 && text((*node)[1]) && text((*node)[2]);
  if (*tag == "bool" || *tag == "index" || *tag == "unit")
    return node->size() == 1;
  if (*tag == "tuple")
    return node->size() == 2 && arguments(1);
  if (*tag == "array")
    return node->size() == 3 &&
           nativeStaticTerm((*node)[1], remaining, depth + 1) &&
           decimal((*node)[2]);
  if (*tag == "nominal") {
    auto kind = node->size() == 4 ? (*node)[1].getAsString() : std::nullopt;
    auto path = node->size() == 4 ? (*node)[2].getAsString() : std::nullopt;
    return kind &&
           (*kind == "record" || *kind == "logical_record" ||
            *kind == "variant" || *kind == "associated" || *kind == "module") &&
           path && staticTermPath(*path) && arguments(3);
  }
  if (*tag == "builtin" || *tag == "formal")
    return node->size() == 3 && text((*node)[1]) && arguments(2);
  return false;
}
Error declarations(const J &value, uint64_t &remaining, bool wire,
                   mlir::MLIRContext *context = nullptr) {
  auto rows = value.getAsArray();
  if (!rows || rows->size() != 3 || !(*rows)[0].getAsArray() ||
      !(*rows)[1].getAsArray() || !(*rows)[2].getAsArray())
    return error("component-declaration");
  auto validString = [wire](const J &value) {
    auto text = value.getAsString();
    return text && !text->empty() && (!wire || text->size() <= 512) &&
           json::isUTF8(*text) && !text->contains('\0');
  };
  std::function<bool(const J &, unsigned)> bounded = [&](const J &value,
                                                         unsigned depth) {
    if (!remaining || depth > 128)
      return false;
    --remaining;
    if (!value.belongsTo(context))
      return false;
    if (!wire) {
      auto text = value.getAsString();
      if (text) {
        if (text->size() > remaining)
          return false;
        remaining -= text->size();
      }
    }
    if (auto items = value.getAsArray())
      for (const auto &item : *items)
        if (!bounded(item, depth + 1))
          return false;
    return true;
  };
  if (!bounded(value, 0))
    return error("component-declaration-limit");
  auto checkTerm = [&](const J &term) -> Error {
    if (wire)
      return checkStaticTerm(*term.jsonValue());
    return nativeStaticTerm(term, remaining) ? Error::success()
                                             : error("source.static-term");
  };
  std::set<J::Key> types;
  std::set<std::string> owners;
  std::map<std::string, StringRef> nominalKinds;
  std::map<J::Key, A> declarations;
  // A placement names roles. A record member's formula ranges over its row's
  // telescope; a port's tree ranges over its protocol's roster, which only
  // the exporter knows. Product arguments are an injective substitution in
  // telescope order. `used` receives the top-level participant summary.
  std::function<Error(const J &, const std::set<std::string> *,
                      std::set<std::string> *, unsigned)>
      placement = [&](const J &value, const std::set<std::string> *telescope,
                      std::set<std::string> *used, unsigned depth) -> Error {
    if (!remaining || depth > 64)
      return error("component-declaration-limit");
    --remaining;
    auto node = value.getAsArray();
    if (!node || node->empty() || !(*node)[0].getAsString())
      return error("component-declaration-placement");
    auto names = [&](const J &list, bool injective,
                     bool summary) -> Expected<std::set<std::string>> {
      auto items = list.getAsArray();
      if (!items || items->size() > protocol::instances::protocolRoleLimit)
        return error("component-declaration-placement");
      std::set<std::string> result;
      for (const auto &item : *items) {
        if (!validString(item) ||
            (telescope && !telescope->count(string(item).str())))
          return error("component-declaration-role");
        if (!result.insert(string(item).str()).second && injective)
          return error("component-declaration-role");
        if (summary && used)
          used->insert(string(item).str());
      }
      return result;
    };
    auto tag = string((*node)[0]);
    if (tag == "data") {
      if (node->size() != 2)
        return error("component-declaration-placement");
      auto roles = names((*node)[1], true, true);
      return roles ? Error::success() : roles.takeError();
    }
    if (tag == "oracle") {
      if (node->size() != 3)
        return error("component-declaration-placement");
      const auto &holder = (*node)[1];
      if (!validString(holder) ||
          (telescope && !telescope->count(string(holder).str())))
        return error("component-declaration-role");
      auto receivers = names((*node)[2], true, true);
      if (!receivers)
        return receivers.takeError();
      if (receivers->count(string(holder).str()))
        return error("component-declaration-role");
      if (used)
        used->insert(string(holder).str());
      return Error::success();
    }
    if (tag != "product" || node->size() != 3 || !(*node)[2].getAsArray() ||
        (wire && array((*node)[2]).size() > 512))
      return error("component-declaration-placement");
    auto arguments = names((*node)[1], true, true);
    if (!arguments)
      return arguments.takeError();
    for (const auto &field : array((*node)[2]))
      if (auto e = placement(field, telescope, nullptr, depth + 1))
        return e;
    return Error::success();
  };
  auto fields = [&](const A &members, bool placed,
                    const std::set<std::string> &telescope) -> Error {
    if (wire && members.size() > 512)
      return error("component-declaration-limit");
    std::set<std::string> names;
    for (const auto &value : members) {
      auto field = value.getAsArray();
      if (!field || field->size() != 3 || !validString((*field)[0]))
        return error("component-declaration");
      if (!names.insert(string((*field)[0]).str()).second)
        return error("component-declaration-duplicate");
      if (auto e = checkTerm((*field)[1]))
        return e;
      // Placement is present exactly for the members of a logical record
      // with a role telescope; its formula ranges over that telescope.
      if (((*field)[2].isNull()) == placed)
        return error("component-declaration-placement");
      if (placed)
        if (auto e = placement((*field)[2], &telescope, nullptr, 0))
          return e;
    }
    return Error::success();
  };
  if (wire &&
      (array((*rows)[0]).size() > 128 || array((*rows)[1]).size() > 128))
    return error("component-declaration-limit");
  for (const auto &value : array((*rows)[0])) {
    auto record = value.getAsArray();
    if (!record || record->size() != 6 || !(*record)[1].getAsString() ||
        !(*record)[2].getAsBoolean() || !(*record)[3].getAsArray() ||
        !(*record)[4].getAsArray())
      return error("component-declaration");
    if (auto e = checkTerm((*record)[0]))
      return e;
    auto type = (*record)[0].getAsArray();
    if (!type || type->size() != 4 || (*type)[0] != J("nominal") ||
        ((*type)[1] != J("record") && (*type)[1] != J("logical_record") &&
         (*type)[1] != J("variant")))
      return error("component-declaration-record");
    auto kind = string((*type)[1]);
    auto [nominal, added] =
        nominalKinds.emplace(string((*type)[2]).str(), kind);
    if (!added && nominal->second != kind)
      return error("component-declaration-record");
    auto identity = (*record)[0].key(remaining);
    if (!identity)
      return identity.takeError();
    if (!types.insert(*identity).second)
      return error("component-declaration-duplicate");
    declarations.emplace(*identity, *record);
    auto resource = string((*record)[1]);
    if (resource != "ordinary" && resource != "affine" && resource != "linear")
      return error("component-declaration");
    // A custody slot names the resource units of exactly the affine and linear
    // rows.
    const auto &slot = (*record)[5];
    if ((resource == "ordinary") != (slot.isNull()) ||
        (!slot.isNull() &&
         (!slot.getAsString() || !string(slot).starts_with("zkl_resource_") ||
          !protocol::resourceUnitDomain(string(slot)))))
      return error("component-declaration-slot");
    // The telescope is the row's own roles in declaration order; only a
    // logical record has one.
    const auto &roles = array((*record)[4]);
    if (roles.size() > protocol::instances::recordRoleLimit)
      return error("component-declaration-limit");
    if (kind != "logical_record" && !roles.empty())
      return error("component-declaration-role");
    std::set<std::string> telescope;
    for (const auto &role : roles)
      if (!validString(role) || !telescope.insert(string(role).str()).second)
        return error("component-declaration-role");
    if (wire && array((*record)[3]).size() > 512)
      return error("component-declaration-limit");
    if (kind != "variant") {
      if (auto e = fields(array((*record)[3]), !telescope.empty(), telescope))
        return e;
      continue;
    }
    std::set<std::string> alternatives;
    for (const auto &value : array((*record)[3])) {
      auto alternative = value.getAsArray();
      if (!alternative || alternative->size() != 2 ||
          !validString((*alternative)[0]) || !(*alternative)[1].getAsArray())
        return error("component-declaration");
      if (!alternatives.insert(string((*alternative)[0]).str()).second)
        return error("component-declaration-duplicate");
      if (auto e = fields(array((*alternative)[1]), false, telescope))
        return e;
    }
  }
  // Retain every nominal child, including children with no physical leaves.
  std::function<Error(const J &, unsigned)> referenced =
      [&](const J &value, unsigned depth) -> Error {
    if (!remaining || depth > 64)
      return error("component-declaration-limit");
    --remaining;
    const auto &term = array(value);
    auto tag = string(term[0]);
    std::optional<A> arguments;
    if (tag == "nominal") {
      auto kind = string(term[1]);
      if (kind == "record" || kind == "logical_record" || kind == "variant") {
        auto identity = value.key(remaining);
        if (!identity)
          return identity.takeError();
        if (!declarations.count(*identity))
          return error("component-declaration-record");
      }
      arguments = array(term[3]);
    } else if (tag == "array" || tag == "descriptor-sequence")
      return referenced(term[1], depth + 1);
    else if (tag == "tuple" || tag == "descriptor-product")
      arguments = array(term[1]);
    else if (tag == "builtin" || tag == "formal")
      arguments = array(term[2]);
    if (arguments)
      for (const auto &argument : *arguments)
        if (auto e = referenced(argument, depth + 1))
          return e;
    return Error::success();
  };
  for (const auto &[identity, declaration] : declarations) {
    if (auto e = referenced(declaration[0], 0))
      return e;
    bool variant = array(declaration[0])[1] == J("variant");
    for (const auto &member : array(declaration[3])) {
      if (variant) {
        for (const auto &field : array(array(member)[1]))
          if (auto e = referenced(array(field)[1], 0))
            return e;
      } else if (auto e = referenced(array(member)[1], 0))
        return e;
    }
  }
  // Ordinary carriers cannot hide distributed logical category, including
  // children erased by zero-length layouts. Distributed records may contain
  // nested records and restrictions; source comparison checks their authority.
  std::set<J::Key> checkedOrdinary;
  std::function<Error(const J &, unsigned)> ordinaryCategory =
      [&](const J &value, unsigned depth) -> Error {
    if (!remaining || depth > 64)
      return error("component-declaration-limit");
    --remaining;
    const auto &term = array(value);
    auto tag = string(term[0]);
    std::optional<A> arguments;
    if (tag == "descriptor-product" || tag == "descriptor-sequence")
      return error("component-declaration-record");
    if (tag == "nominal") {
      auto kind = string(term[1]);
      if (kind == "logical_record")
        return error("component-declaration-record");
      if (kind == "record" || kind == "variant") {
        auto identity = value.key(remaining);
        if (!identity)
          return identity.takeError();
        auto found = declarations.find(*identity);
        if (found == declarations.end())
          return error("component-declaration-record");
        if (!checkedOrdinary.insert(*identity).second)
          return Error::success();
        const auto &members = array(found->second[3]);
        if (kind == "variant") {
          for (const auto &alternative : members)
            for (const auto &field : array(array(alternative)[1]))
              if (auto e = ordinaryCategory(array(field)[1], depth + 1))
                return e;
        } else
          for (const auto &field : members)
            if (auto e = ordinaryCategory(array(field)[1], depth + 1))
              return e;
        // Logical category is checked before physical expansion, including
        // phantom arguments. An ordinary carrier cannot erase that category.
        for (const auto &argument : array(term[3]))
          if (auto e = ordinaryCategory(argument, depth + 1))
            return e;
        return Error::success();
      }
      arguments = array(term[3]);
    } else if (tag == "array") {
      return ordinaryCategory(term[1], depth + 1);
    } else if (tag == "tuple")
      arguments = array(term[1]);
    else if (tag == "builtin" || tag == "formal") {
      // A head that a frontend constructor row spells is a logical handle.
      if (tag == "builtin" && protocol::frontendConstructor(string(term[1])))
        return error("component-declaration-record");
      arguments = array(term[2]);
    }
    if (arguments)
      for (const auto &argument : *arguments)
        if (auto e = ordinaryCategory(argument, depth + 1))
          return e;
    return Error::success();
  };
  for (const auto &[identity, declaration] : declarations)
    if (array(declaration[0])[1] != J("logical_record"))
      if (auto e = ordinaryCategory(declaration[0], 0))
        return e;
  for (const auto &value : array((*rows)[1])) {
    auto owner = value.getAsArray();
    if (!owner || owner->size() != 3 || !validString((*owner)[0]))
      return error("component-declaration");
    if (!owners.insert(string((*owner)[0]).str()).second)
      return error("component-declaration-duplicate");
    for (unsigned side : {1u, 2u}) {
      auto ports = (*owner)[side].getAsArray();
      if (!ports || (wire && ports->size() > 512))
        return error("component-declaration");
      std::set<std::string> names;
      for (const auto &value : *ports) {
        auto port = value.getAsArray();
        if (!port || port->size() != 6 || !validString((*port)[0]) ||
            !(*port)[2].getAsArray() || !(*port)[3].getAsUINT64() ||
            !(*port)[4].getAsUINT64() ||
            (wire && *(*port)[3].getAsUINT64() > 512) ||
            (wire && *(*port)[4].getAsUINT64() > 512))
          return error("component-declaration");
        if (!names.insert(string((*port)[0]).str()).second)
          return error("component-declaration-duplicate");
        if (auto e = checkTerm((*port)[1]))
          return e;
        if (auto e = referenced((*port)[1], 0))
          return e;
        if (array((*port)[2]).size() > protocol::instances::protocolRoleLimit)
          return error("component-declaration-limit");
        std::set<std::string> roles;
        for (const auto &role : array((*port)[2])) {
          if (!validString(role))
            return error("component-declaration-role");
          if (!roles.insert(string(role).str()).second)
            return error("component-declaration-role");
        }
        // The participant list is a derived summary of the placement tree.
        std::set<std::string> placed;
        if (auto e = placement((*port)[5], nullptr, &placed, 0))
          return e;
        if (placed != roles)
          return error("component-declaration-placement");
      }
    }
  }
  // One authority row per nominal record, logical record, variant and module
  // path in any carrier term, sorted by path. A revision is a SHA-256 hex
  // digest; null marks a generated declaration.
  std::set<std::string> paths;
  std::function<Error(const J &, unsigned)> nominal =
      [&](const J &value, unsigned depth) -> Error {
    if (!remaining || depth > 64)
      return error("component-declaration-limit");
    --remaining;
    const auto &term = array(value);
    auto tag = string(term[0]);
    std::optional<A> arguments;
    if (tag == "nominal") {
      auto kind = string(term[1]);
      if (kind == "record" || kind == "logical_record" || kind == "variant" ||
          kind == "module")
        paths.insert(string(term[2]).str());
      arguments = array(term[3]);
    } else if (tag == "array" || tag == "descriptor-sequence")
      return nominal(term[1], depth + 1);
    else if (tag == "tuple" || tag == "descriptor-product")
      arguments = array(term[1]);
    else if (tag == "builtin" || tag == "formal")
      arguments = array(term[2]);
    if (arguments)
      for (const auto &argument : *arguments)
        if (auto e = nominal(argument, depth + 1))
          return e;
    return Error::success();
  };
  for (const auto &[identity, declaration] : declarations) {
    if (auto e = nominal(declaration[0], 0))
      return e;
    bool variant = array(declaration[0])[1] == J("variant");
    for (const auto &member : array(declaration[3])) {
      if (variant) {
        for (const auto &field : array(array(member)[1]))
          if (auto e = nominal(array(field)[1], 0))
            return e;
      } else if (auto e = nominal(array(member)[1], 0))
        return e;
    }
  }
  for (const auto &value : array((*rows)[1]))
    for (unsigned side : {1u, 2u})
      for (const auto &port : array(array(value)[side]))
        if (auto e = nominal(array(port)[1], 0))
          return e;
  const auto &authorities = array((*rows)[2]);
  if (authorities.size() != paths.size())
    return error("component-declaration-authority");
  auto expected = paths.begin();
  for (const auto &value : authorities) {
    auto row = value.getAsArray();
    if (!row || row->size() != 2 || !validString((*row)[0]) ||
        string((*row)[0]) != *expected++)
      return error("component-declaration-authority");
    const auto &revision = (*row)[1];
    if (revision.isNull())
      continue;
    auto digest = revision.getAsString();
    if (!digest || digest->size() != 64 || !llvm::all_of(*digest, [](char c) {
          return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
        }))
      return error("component-declaration-authority");
  }
  return Error::success();
}
} // namespace
Error checkComponentDeclarations(const json::Value &value) {
  uint64_t remaining = 1048576;
  return declarations(DeclarationValue(value), remaining, true);
}
Error checkComponentDeclarations(mlir::Attribute value,
                                 protocol::SourceAllowance &allowance) {
  if (!value)
    return error("component-declaration");
  return declarations(DeclarationValue(value), allowance.remaining, false,
                      value.getContext());
}
} // namespace zkc::language
