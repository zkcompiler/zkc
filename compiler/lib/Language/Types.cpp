#include "zkc/Language/Types.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
namespace zkc::language {
StringRef typeKindName(Type::Kind kind) {
  switch (kind) {
  case Type::Kind::Boolean:
    return "boolean";
  case Type::Kind::Field:
    return "field";
  case Type::Kind::Group:
    return "group";
  case Type::Kind::Index:
    return "index";
  case Type::Kind::Unit:
    return "unit";
  case Type::Kind::Tuple:
    return "tuple";
  case Type::Kind::Array:
    return "array";
  case Type::Kind::Record:
    return "record";
  case Type::Kind::Variant:
    return "variant";
  case Type::Kind::Parameter:
    return "parameter";
  case Type::Kind::Associated:
    return "associated";
  case Type::Kind::Natural:
    return "natural";
  case Type::Kind::Component:
    return "component";
  case Type::Kind::Builtin:
    return "builtin";
  case Type::Kind::Formal:
    return "formal";
  }
  llvm_unreachable("unknown source type kind");
}

std::string spelling(const Type &type) {
  using K = Type::Kind;
  switch (type.kind) {
  case K::Boolean:
    return "bool";
  case K::Index:
    return "index";
  case K::Unit:
    return "()";
  case K::Natural:
    return type.dimension.spelling();
  default:
    break;
  }
  if (type.kind == K::Builtin || type.kind == K::Formal) {
    std::string result =
        std::string(type.kind == K::Formal ? "formal(\"" : "builtin(\"") +
        type.domain + "\"";
    for (const auto &argument : type.arguments)
      result += ", " + spelling(argument);
    return result + ")";
  }
  if (type.kind == K::Array)
    return "[" + spelling(type.arguments.front()) + "; " +
           type.dimension.spelling() + "]";
  std::string result =
      type.kind == K::Tuple                     ? "("
      : type.kind == K::Field && !type.symbolic ? "field<" + type.domain + ">"
      : type.kind == K::Group && !type.symbolic ? "group<" + type.domain + ">"
                                                : type.domain;
  if (!type.arguments.empty()) {
    if (type.kind != K::Tuple)
      result += "<";
    for (unsigned i = 0; i < type.arguments.size(); ++i) {
      if (i)
        result += ", ";
      result += spelling(type.arguments[i]);
    }
    if (type.kind == K::Tuple && type.arguments.size() == 1)
      result += ",";
    result += type.kind == K::Tuple ? ")" : ">";
  }
  return result;
}
std::string typeIdentity(const Type &type) {
  std::string result;
  raw_string_ostream out(result);
  auto frame = [&](StringRef value) { out << value.size() << ':' << value; };
  out << static_cast<unsigned>(type.kind) << ':';
  if (type.kind == Type::Kind::Natural) {
    frame(type.dimension.spelling());
    return result;
  }
  out << type.symbolic << ':';
  frame(type.domain);
  frame(type.dimension.spelling());
  out << type.arguments.size() << ':';
  for (const auto &argument : type.arguments)
    frame(typeIdentity(argument));
  return result;
}
Expected<uint64_t> typeComplexity(const Type &type, uint64_t nodes,
                                  uint64_t depth) {
  uint64_t cost = 0;
  std::function<Error(const Type &, uint64_t)> visit =
      [&](const Type &term, uint64_t level) -> Error {
    if (!nodes || level > depth)
      return error("source.limit", "expanded source type limit exceeded");
    --nodes;
    cost += 1 + term.domain.size();
    for (auto &[factors, coefficient] : term.dimension.terms()) {
      (void)coefficient;
      cost += 1;
      for (auto &factor : factors)
        cost += 1 + factor.name.size();
    }
    for (auto &argument : term.arguments)
      if (auto e = visit(argument, level + 1))
        return e;
    return Error::success();
  };
  if (auto e = visit(type, 1))
    return std::move(e);
  return cost;
}
} // namespace zkc::language
