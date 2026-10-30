#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <functional>

using namespace llvm;
namespace zkc::protocol {
namespace {
bool name(StringRef value) {
  return !value.empty() && value.size() <= 256 &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-' || c == '/';
         });
}
Expected<BoundType> formPhysicalType(const BoundType &, StringRef,
                                     std::vector<BoundType>);
Expected<StringRef> defaultRepresentationIdentity(const BoundType &logical) {
  if (logical.kind == "sequence")
    return "logical.sequence/0";
  if (logical.kind == "variant")
    return "logical.variant/0";
  if (logical.kind == "resource_unit")
    return "logical.resource_unit/0";
  if (!logical.arguments.empty()) {
    auto entry = appliedTypeRepresentation(logical);
    if (!entry)
      return error("binding-representation");
    return entry->representation;
  }
  auto entry =
      installedDomains().defaultRepresentation(logical.kind, logical.identity);
  if (!entry)
    return error("binding-representation");
  return entry->identity;
}
bool defaultLayout(const BoundType &type) {
  auto identity = defaultRepresentationIdentity(type);
  if (!identity) {
    consumeError(identity.takeError());
    return false;
  }
  return type.representation == *identity &&
         (!type.physicalChildren ||
          all_of(*type.physicalChildren, defaultLayout));
}
} // namespace
bool BoundType::operator==(const BoundType &other) const {
  return kind == other.kind && identity == other.identity &&
         representation == other.representation &&
         arguments == other.arguments &&
         (physicalChildren == other.physicalChildren ||
          (physicalChildren && other.physicalChildren &&
           *physicalChildren == *other.physicalChildren));
}

TypeArgument TypeArgument::domainArgument(std::string identity) {
  return {Kind::Domain, std::move(identity), {}, 0};
}
TypeArgument TypeArgument::typeArgument(BoundType value) {
  return {
      Kind::Type, {}, std::make_shared<const BoundType>(std::move(value)), 0};
}
TypeArgument TypeArgument::naturalArgument(uint64_t value) {
  return {Kind::Nat, {}, {}, value};
}
bool TypeArgument::operator==(const TypeArgument &other) const {
  if (kind != other.kind)
    return false;
  switch (kind) {
  case Kind::Domain:
    return domain == other.domain;
  case Kind::Nat:
    return natural == other.natural;
  case Kind::Type:
    return type && other.type && *type == *other.type;
  }
  llvm_unreachable("invalid argument kind");
}
std::string TypeArgument::spelling() const {
  switch (kind) {
  case Kind::Domain:
    return domain;
  case Kind::Nat:
    return std::to_string(natural);
  case Kind::Type:
    return type ? type->spelling() : std::string{};
  }
  llvm_unreachable("invalid argument kind");
}

std::string BoundType::spelling() const {
  std::string result = kind;
  if (arguments.empty())
    result += identity.empty() ? "" : ":" + identity;
  else {
    result += '<';
    for (auto [i, argument] : enumerate(arguments)) {
      if (i)
        result += ',';
      result += argument.spelling();
    }
    result += '>';
  }
  if (representation.empty())
    return result;
  std::function<std::string(const BoundType &)> layout =
      [&](const BoundType &t) {
        std::string out = t.representation;
        if (t.physicalChildren) {
          bool defaults = all_of(*t.physicalChildren, defaultLayout);
          if (!defaults) {
            out += '[';
            for (auto [i, child] : enumerate(*t.physicalChildren)) {
              if (i)
                out += ',';
              out += layout(child);
            }
            out += ']';
          }
        }
        return out;
      };
  return result + "@" + layout(*this);
}

Expected<TypeApplication> splitTypeApplication(StringRef text) {
  if (text.empty() || text.size() > 4096 || text.contains('@'))
    return error("binding-type");
  auto open = text.find('<');
  auto colon = text.find(':');
  if (open == StringRef::npos || colon < open) {
    if (text.contains('<') || text.contains('>') || text.contains(','))
      return error("binding-type");
    auto pair = text.split(':');
    TypeApplication result{pair.first.str(), {}};
    if (colon != StringRef::npos) {
      if (pair.second.empty())
        return error("binding-type-identity");
      result.arguments.push_back(pair.second.str());
    }
    return result;
  }
  if (!text.ends_with(">"))
    return error("binding-type-identity");
  const auto *declaration = typeDeclaration(text.take_front(open));
  if (!declaration || declaration->parameters.empty() ||
      (declaration->parameters.size() == 1 &&
       declaration->parameters[0].kind == StaticKind::Domain))
    return error("binding-type-identity");
  TypeApplication result{text.take_front(open).str(), {}};
  auto body = text.slice(open + 1, text.size() - 1);
  unsigned nesting = 0;
  size_t start = 0;
  for (size_t i = 0; i <= body.size(); ++i) {
    if (i == body.size() || (body[i] == ',' && !nesting)) {
      if (i == start ||
          result.arguments.size() >= declaration->parameters.size())
        return error("binding-type-identity");
      result.arguments.push_back(body.slice(start, i).str());
      start = i + 1;
    } else if (body[i] == '<') {
      if (++nesting >= 8)
        return error("binding-type-limit");
    } else if (body[i] == '>') {
      if (!nesting)
        return error("binding-type-identity");
      --nesting;
    }
  }
  if (nesting || result.arguments.size() != declaration->parameters.size())
    return error("binding-type-identity");
  return result;
}

Expected<BoundType> parseBoundType(StringRef spelling, bool physical,
                                   unsigned depth, TypeParseBudget *budget) {
  TypeParseBudget localBudget;
  if (!budget)
    budget = &localBudget;
  if (physical) {
    if (spelling.size() > PhysicalSpellingBytes)
      return error("binding-type-limit");
    auto [logicalText, layout] = spelling.split('@');
    if (!spelling.contains('@'))
      return error("binding-representation");
    auto logical = parseBoundType(logicalText, false, depth, budget);
    if (!logical)
      return logical.takeError();
    std::function<Expected<BoundType>(const BoundType &, StringRef, unsigned)>
        read;
    read = [&](const BoundType &schema, StringRef text,
               unsigned level) -> Expected<BoundType> {
      if (level > 8 || !budget->consume() ||
          !budget->charge(sizeof(BoundType) + text.size() +
                          schema.spelling().size()))
        return error("binding-type-limit");
      auto open = text.find('[');
      auto rep = text.take_front(open);
      if (!name(rep))
        return error("binding-representation");
      auto schemas = logicalChildren(schema);
      if (!schemas)
        return schemas.takeError();
      bool aggregate = schema.kind == "sequence" || schema.kind == "variant" ||
                       schema.kind == "field_array" ||
                       schema.kind == "fixed_vector";
      std::vector<BoundType> children;
      if (!budget->charge(schemas->size() * sizeof(BoundType)))
        return error("binding-type-limit");
      children.reserve(schemas->size());
      if (open == StringRef::npos) {
        for (const auto &child : *schemas) {
          auto identity = defaultRepresentationIdentity(child);
          if (!identity)
            return identity.takeError();
          // Form omitted default children directly under the shared allowance.
          auto selected = read(child, *identity, level + 1);
          if (!selected)
            return selected.takeError();
          children.push_back(std::move(*selected));
        }
      } else {
        if (!aggregate || !text.ends_with("]"))
          return error("binding-representation");
        auto body = text.slice(open + 1, text.size() - 1);
        size_t start = 0;
        unsigned nesting = 0;
        for (size_t i = 0; i <= body.size(); ++i) {
          if (i == body.size() || (body[i] == ',' && nesting == 0)) {
            if (children.size() >= schemas->size() || i == start)
              return error("binding-representation");
            auto child = read((*schemas)[children.size()], body.slice(start, i),
                              level + 1);
            if (!child)
              return child.takeError();
            children.push_back(std::move(*child));
            start = i + 1;
          } else if (body[i] == '[') {
            if (++nesting + level > 8)
              return error("binding-type-limit");
          } else if (body[i] == ']') {
            if (!nesting)
              return error("binding-representation");
            --nesting;
          }
        }
        if (nesting)
          return error("binding-representation");
      }
      if (children.size() != schemas->size())
        return error("binding-representation");
      auto result = formPhysicalType(schema, rep, std::move(children));
      if (!result)
        return result.takeError();
      return result;
    };
    auto result = read(*logical, layout, depth);
    if (!result)
      return result.takeError();
    if (result->spelling() != spelling)
      return error("binding-representation");
    return result;
  }
  if (spelling.contains('@'))
    return error("binding-representation");
  auto logical = spelling;
  if (logical.size() >
      (logical.starts_with("variant:") ? VariantSpellingBytes : 4096))
    return error("binding-type-limit");
  if (!budget->charge(sizeof(BoundType) + logical.size()))
    return error("binding-type-limit");
  auto [kind, identity] = logical.split(':');
  if (depth > 8 || (!logical.starts_with("variant:") && !budget->consume()))
    return error("binding-type-limit");
  auto open = logical.find('<');
  if (open != StringRef::npos) {
    if (depth >= 8)
      return error("binding-type-limit");
    StringRef head = logical.take_front(open);
    const auto *declaration = typeDeclaration(head);
    if (!declaration)
      return error("binding-type");
    // There is only one canonical spelling per constructor shape.
    if (!logical.ends_with(">") || declaration->parameters.empty() ||
        (declaration->parameters.size() == 1 &&
         declaration->parameters[0].kind == StaticKind::Domain))
      return error("binding-type-identity");
    StringRef body = logical.drop_front(open + 1).drop_back();
    SmallVector<StringRef> arguments;
    size_t start = 0;
    unsigned nesting = 0;
    for (size_t i = 0; i < body.size(); ++i) {
      if (body[i] == '<') {
        if (++nesting + depth >= 8)
          return error("binding-type-limit");
      } else if (body[i] == '>') {
        if (!nesting)
          return error("binding-type-identity");
        --nesting;
      } else if (body[i] == ',' && !nesting) {
        arguments.push_back(body.slice(start, i));
        start = i + 1;
      }
    }
    if (nesting)
      return error("binding-type-identity");
    arguments.push_back(body.drop_front(start));
    if (arguments.size() != declaration->parameters.size())
      return error("binding-type-identity");
    if (!budget->charge(arguments.size() * sizeof(TypeArgument)))
      return error("binding-type-limit");
    BoundType result{head.str(), {}, {}};
    for (auto [argument, parameter] : zip(arguments, declaration->parameters)) {
      switch (parameter.kind) {
      case StaticKind::Domain:
        if (!budget->consume())
          return error("binding-type-limit");
        if (installedIdentitySort(argument) != parameter.sort)
          return error("binding-type-identity");
        result.arguments.push_back(
            TypeArgument::domainArgument(argument.str()));
        break;
      case StaticKind::Type: {
        auto element = parseBoundType(argument, false, depth + 1, budget);
        if (!element)
          return element.takeError();
        result.arguments.push_back(
            TypeArgument::typeArgument(std::move(*element)));
        break;
      }
      case StaticKind::Nat: {
        if (!budget->consume())
          return error("binding-type-limit");
        uint64_t n;
        if (argument.empty() ||
            (argument.size() > 1 && argument.front() == '0') ||
            !all_of(argument, [](char c) { return isDigit(c); }) ||
            argument.getAsInteger(10, n))
          return error("binding-type-identity");
        if (n > 1048576)
          return error("binding-type-limit");
        result.arguments.push_back(TypeArgument::naturalArgument(n));
        break;
      }
      }
    }
    if (result.spelling() != spelling)
      return error("binding-type-identity");
    if (head == "sequence") {
      auto &element = *result.arguments.front().type;
      if (!duplicable(element) || !discardable(element))
        return error("sequence-element-permission");
    }
    return result;
  }
  if (kind == "variant") {
    auto descriptor = decodeVariant(logical.str(), depth, budget);
    if (!descriptor)
      return error("variant-type");
    return BoundType{kind.str(), identity.str(), {}};
  }
  if (kind == "resource_unit") {
    if (!resourceUnitDomain(identity))
      return error("binding-type-identity");
    return BoundType{kind.str(), identity.str(), {}};
  }
  for (const auto &t : boundTypeConstructors()) {
    if (t.name != kind)
      continue;
    const auto *declaration = typeDeclaration(kind);
    if (!declaration || declaration->parameters.size() > 1 ||
        (declaration->parameters.size() == 1 &&
         declaration->parameters[0].kind != StaticKind::Domain))
      return error("binding-type-identity");
    if (t.parameters.empty()
            ? !identity.empty() || logical.contains(':')
            : installedDomains().identitySort(identity) != t.parameters[0])
      return error("binding-type-identity");
    // Sort agreement alone does not admit a logical instance. Formation uses
    // explicit catalog data, independently of physical representation support.
    if (!installedDomains().admitsLogicalType(kind, identity))
      return error("binding-type-identity");
    return BoundType{kind.str(), identity.str(), {}};
  }
  return error("binding-type");
}

BoundType erasePhysicalType(const BoundType &type) {
  auto result = type;
  result.representation.clear();
  result.physicalChildren.reset();
  for (auto &argument : result.arguments)
    if (argument.kind == TypeArgument::Kind::Type && argument.type)
      argument.type =
          std::make_shared<const BoundType>(erasePhysicalType(*argument.type));
  return result;
}

Expected<std::vector<BoundType>> logicalChildren(const BoundType &logical) {
  std::vector<BoundType> result;
  if (logical.kind == "sequence" || logical.kind == "fixed_vector") {
    if (logical.arguments.empty() || !logical.arguments[0].type)
      return error("binding-type-identity");
    result.push_back(*logical.arguments[0].type);
  } else if (logical.kind == "field_array") {
    if (logical.arguments.empty())
      return error("binding-type-identity");
    auto field = parseBoundType("field:" + logical.arguments[0].domain, false);
    if (!field)
      return field.takeError();
    result.push_back(std::move(*field));
  } else if (logical.kind == "variant") {
    auto descriptor = decodeVariant(logical.spelling());
    if (!descriptor)
      return error("variant-type");
    for (const auto &arm : descriptor->alternatives)
      for (const auto &payload : arm.payload) {
        auto type = parseBoundType(payload, false);
        if (!type)
          return type.takeError();
        result.push_back(std::move(*type));
      }
  }
  return result;
}

namespace {
Expected<BoundType> formPhysicalType(const BoundType &logical,
                                     StringRef representation,
                                     std::vector<BoundType> children) {
  auto schemas = logicalChildren(logical);
  if (!schemas)
    return schemas.takeError();
  bool aggregate = logical.kind == "sequence" || logical.kind == "variant" ||
                   logical.kind == "field_array" ||
                   logical.kind == "fixed_vector";
  if (!name(representation) || children.size() != schemas->size())
    return error("binding-representation");
  for (auto [child, schema] : zip(children, *schemas))
    if (child.representation.empty() || !(erasePhysicalType(child) == schema))
      return error("binding-representation");
  if (logical.kind == "sequence" || logical.kind == "variant") {
    if (representation != (logical.kind == "sequence" ? "logical.sequence/0"
                                                      : "logical.variant/0"))
      return error("binding-representation");
  } else if (logical.kind == "field_array" || logical.kind == "fixed_vector") {
    const auto *descriptor = appliedTypeRepresentation(logical, representation);
    if (!descriptor)
      return error("binding-representation");
    auto expected = parseBoundType(descriptor->childType, true);
    if (!expected)
      return expected.takeError();
    if (children.size() != 1 || !(children[0] == *expected))
      return error("binding-representation");
  } else if (logical.kind == "resource_unit") {
    if (representation != "logical.resource_unit/0")
      return error("binding-representation");
  } else if (!installedDomains().representation(logical.kind, logical.identity,
                                                representation))
    return error("binding-representation");
  auto result = logical;
  result.representation = representation.str();
  if (aggregate)
    result.physicalChildren =
        std::make_shared<const std::vector<BoundType>>(std::move(children));
  return result;
}
} // namespace

Expected<BoundType> physicalType(const BoundType &logical,
                                 StringRef representation,
                                 std::vector<BoundType> children) {
  auto checked = parseBoundType(logical.spelling(), false);
  if (!checked)
    return checked.takeError();
  if (!(*checked == logical))
    return error("binding-type-identity");
  for (const auto &child : children) {
    auto admitted = parseBoundType(child.spelling(), true);
    if (!admitted)
      return admitted.takeError();
    if (!(*admitted == child))
      return error("binding-representation");
  }
  auto result = formPhysicalType(logical, representation, std::move(children));
  if (!result)
    return result.takeError();
  auto admitted = parseBoundType(result->spelling(), true);
  if (!admitted)
    return admitted.takeError();
  if (!(*admitted == *result))
    return error("binding-representation");
  return result;
}

Expected<BoundType> defaultRepresentation(const BoundType &logical) {
  if (!logical.representation.empty() || logical.physicalChildren)
    return error("binding-physical-type-at-logical-stage");
  auto checked = parseBoundType(logical.spelling(), false);
  if (!checked)
    return checked.takeError();
  if (!(*checked == logical))
    return error("binding-type-identity");
  auto schemas = logicalChildren(logical);
  if (!schemas)
    return schemas.takeError();
  std::vector<BoundType> children;
  for (const auto &schema : *schemas) {
    auto child = defaultRepresentation(schema);
    if (!child)
      return child.takeError();
    children.push_back(std::move(*child));
  }
  auto representation = defaultRepresentationIdentity(logical);
  if (!representation)
    return representation.takeError();
  return formPhysicalType(logical, *representation, std::move(children));
}

Expected<BoundType> applyBoundType(StringRef constructor,
                                   ArrayRef<std::string> arguments) {
  const auto *declaration = typeDeclaration(constructor);
  if (!declaration)
    return error("binding-type");
  if (arguments.size() != declaration->parameters.size())
    return error("binding-type-identity");
  std::string spelling = constructor.str();
  if (arguments.size() == 1 &&
      declaration->parameters[0].kind == StaticKind::Domain)
    spelling += ':' + arguments.front();
  else if (!arguments.empty()) {
    spelling += '<';
    for (auto [i, argument] : enumerate(arguments)) {
      if (i)
        spelling += ',';
      spelling += argument;
    }
    spelling += '>';
  }
  return parseBoundType(spelling, false);
}
} // namespace zkc::protocol
