#include "zkc/Language/SourceTerms.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::language {
namespace {
Expected<json::Value> encode(const Type &type, unsigned &remaining,
                             unsigned depth = 0) {
  using K = Type::Kind;
  if (!remaining || depth >= 64)
    return error("source.limit", "static term limit exceeded");
  --remaining;
  if (type.symbolic || type.kind == K::Parameter)
    return error("source.static-term", "static term is not closed");
  if (type.domain.size() > 512 || type.sort.size() > 512)
    return error("source.limit", "static term string exceeds 512 bytes");
  if (type.kind == K::Natural) {
    if (!type.dimension.isClosed())
      return error("source.static-term", "natural is not closed");
    return json::Array{"nat", std::to_string(type.dimension.closedValue())};
  }
  if (type.kind == K::Boolean || type.kind == K::Index || type.kind == K::Unit)
    return json::Array{type.kind == K::Boolean ? "bool"
                       : type.kind == K::Index ? "index"
                                               : "unit"};
  if (type.kind == K::Field || type.kind == K::Group)
    return json::Array{type.kind == K::Field ? "field" : "group", type.domain};
  if (type.kind == K::Domain || type.kind == K::Asset)
    return json::Array{type.kind == K::Domain ? "domain" : "asset", type.sort,
                       type.domain};
  if (type.kind == K::Array) {
    if (type.arguments.size() != 1 || !type.dimension.isClosed())
      return error("source.static-term", "array is not closed");
    auto element = encode(type.arguments.front(), remaining, depth + 1);
    if (!element)
      return element.takeError();
    return json::Array{"array", std::move(*element),
                       std::to_string(type.dimension.closedValue())};
  }
  json::Array arguments;
  if (type.arguments.size() > 512 || type.arguments.size() > remaining)
    return error("source.limit", "static term node limit exceeded");
  for (const auto &argument : type.arguments) {
    auto value = encode(argument, remaining, depth + 1);
    if (!value)
      return value.takeError();
    arguments.push_back(std::move(*value));
  }
  if (type.kind == K::Tuple)
    return json::Array{"tuple", std::move(arguments)};
  if (type.kind == K::Builtin || type.kind == K::Formal)
    return json::Array{type.kind == K::Builtin ? "builtin" : "formal",
                       type.domain, std::move(arguments)};
  if (type.kind == K::Record || type.kind == K::Variant ||
      type.kind == K::Associated || type.kind == K::Module)
    return json::Array{"nominal", typeKindName(type.kind), type.domain,
                       std::move(arguments)};
  return error("source.static-term", "unsupported static term");
}
} // namespace
Expected<json::Value> encodeStaticTerm(const Type &type) {
  unsigned remaining = 4096;
  auto value = encode(type, remaining);
  if (!value)
    return value.takeError();
  if (auto e = checkStaticTerm(*value))
    return std::move(e);
  return std::move(*value);
}
Expected<json::Value> encodeProtocolOrigin(const ClosedEntry &entry,
                                           const Declaration &decl) {
  const auto &source =
      decl.origin ? entry.declarations()[decl.origin->index] : decl;
  if (source.parameters.size() != decl.staticArguments.size())
    return error("source.protocol-origin", "static argument count differs");
  if (source.qualifiedName.size() > 2048 || source.parameters.size() > 128)
    return error("source.limit", "protocol origin limit exceeded");
  json::Array bindings;
  unsigned remaining = 4096;
  for (unsigned i = 0; i < source.parameters.size(); ++i) {
    auto term = encode(decl.staticArguments[i], remaining);
    if (!term)
      return term.takeError();
    bindings.push_back(
        json::Array{source.parameters[i].name, std::move(*term)});
  }
  json::Value value = json::Array{source.qualifiedName, std::move(bindings)};
  if (auto e = checkProtocolOrigin(value))
    return std::move(e);
  return value;
}
} // namespace zkc::language
