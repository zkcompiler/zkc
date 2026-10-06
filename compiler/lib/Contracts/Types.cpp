#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"

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
} // namespace
bool BoundType::operator==(const BoundType &other) const {
  return kind == other.kind && identity == other.identity &&
         representation == other.representation && arguments == other.arguments;
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
  return result + (representation.empty() ? "" : "@" + representation);
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
  auto [logical, rep] = spelling.split('@');
  if (logical.size() >
      (logical.starts_with("variant:") ? VariantSpellingBytes : 4096))
    return error("binding-type-limit");
  auto [kind, identity] = logical.split(':');
  if (depth > 8 || (!logical.starts_with("variant:") && !budget->consume()))
    return error("binding-type-limit");
  if (physical != spelling.contains('@') || (physical && !name(rep)))
    return error("binding-representation");
  auto open = logical.find('<');
  if (open != StringRef::npos) {
    if (depth >= 8)
      return error("binding-type-limit");
    StringRef head = logical.take_front(open);
    const auto *declaration = typeDeclaration(head);
    if (!declaration || !declaration->common)
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
    BoundType result{head.str(), {}, rep.str()};
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
      if (physical) {
        if (rep != "logical.sequence/1")
          return error("binding-representation");
        auto selected = defaultRepresentation(element);
        if (!selected)
          return selected.takeError();
      }
    } else if (physical && !appliedTypeRepresentation(result, rep))
      return error("binding-representation");
    return result;
  }
  if (kind == "variant") {
    auto descriptor = decodeVariant(logical.str(), depth, budget);
    if (!descriptor)
      return error("variant-type");
    if (physical && rep != "logical.variant/1")
      return error("binding-representation");
    if (physical)
      for (const auto &arm : descriptor->alternatives)
        for (const auto &leaf : arm.payload) {
          auto parsed = parseBoundType(leaf, false, depth + 1);
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
  if (!(*checked == logical))
    return error("binding-type-identity");
  if (logical.kind == "sequence")
    return parseBoundType(logical.spelling() + "@logical.sequence/1", true);
  if (!logical.arguments.empty()) {
    const auto *entry = appliedTypeRepresentation(logical);
    if (!entry)
      return error("binding-representation");
    return parseBoundType(
        logical.spelling() + "@" + entry->representation.str(), true);
  }
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

Expected<BoundType> applyBoundType(StringRef constructor,
                                   ArrayRef<std::string> arguments) {
  const auto *declaration = typeDeclaration(constructor);
  if (!declaration || !declaration->common)
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
