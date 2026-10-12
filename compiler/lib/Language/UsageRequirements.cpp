#include "Semantics.h"
#include "zkc/Contracts/Declarations.h"
using namespace llvm;
namespace zkc::language::detail {
bool Semantics::requireUsage(const Type &type, Usage usage, Span span,
                             const Declaration *scope, StringRef code,
                             StringRef message) {
  auto properties = permissions(type, span, scope);
  if (!properties)
    return false;
  if (usage == Usage::Copy ? properties->copy : properties->drop)
    return true;
  if (scope && collectUsage &&
      collectUsage(*scope, type, usage, span, code, message))
    return true;
  return diagnostic ? false : fail(code, message, span);
}
std::optional<std::vector<Type>>
Semantics::usageRequirements(const Type &type, Usage usage, Span span,
                             const Declaration &scope, StringRef code,
                             StringRef message, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "usage requirement depth exceeded", span);
    return {};
  }
  auto properties = permissions(type, span, &scope);
  if (!properties)
    return {};
  if (usage == Usage::Copy ? properties->copy : properties->drop)
    return std::vector<Type>{};
  const auto *nominal = typeDeclaration(type);
  if (nominal && nominal->resource) {
    fail(code, message, span);
    return {};
  }
  if (type.kind == Type::Kind::Parameter ||
      (type.kind == Type::Kind::Associated && nominal && nominal->abstract &&
       symbolic(type))) {
    Type atom = type;
    atom.assumptions = {};
    return std::vector<Type>{std::move(atom)};
  }
  std::vector<Type> children;
  if (type.kind == Type::Kind::Tuple || type.kind == Type::Kind::Array) {
    children = type.arguments;
  } else if (type.kind == Type::Kind::Record ||
             (type.kind == Type::Kind::Associated && nominal &&
              !nominal->abstract)) {
    auto fields = this->fields(type, span, depth + 1);
    if (!fields)
      return {};
    for (const auto &field : *fields)
      children.push_back(field.type);
  } else if (type.kind == Type::Kind::Variant) {
    auto alternatives = this->alternatives(type, span, depth + 1);
    if (!alternatives)
      return {};
    for (const auto &alternative : *alternatives)
      for (const auto &field : alternative.fields)
        children.push_back(field.type);
  } else if (type.kind == Type::Kind::Builtin && symbolic(type)) {
    const auto *native = protocol::typePermissions(type.domain);
    if (!native || !(usage == Usage::Copy ? native->copy : native->drop)) {
      fail(code, message, span);
      return {};
    }
    for (const auto &argument : type.arguments)
      if (!isStaticOnly(argument))
        children.push_back(argument);
  } else {
    fail(code, message, span);
    return {};
  }
  std::vector<Type> result;
  for (const auto &child : children) {
    auto requirements =
        usageRequirements(child, usage, span, scope, code, message, depth + 1);
    if (!requirements)
      return {};
    for (auto &requirement : *requirements)
      if (!is_contained(result, requirement))
        result.push_back(std::move(requirement));
  }
  return result;
}
} // namespace zkc::language::detail
