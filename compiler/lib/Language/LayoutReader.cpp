#include "LayoutReader.h"
#include "FormalSource.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
ArrayRef<LayoutReader::Id> LayoutReader::children(Id id) const {
  return tree.children(id);
}
LayoutReader::K LayoutReader::kind(Id id) const { return tree.node(id).kind; }
Span LayoutReader::span(Id id) const { return tree.span(id); }
Error LayoutReader::fail(Id id, StringRef message, StringRef code) const {
  return failure(code, message, span(id));
}
Error LayoutReader::charge(Id id) { return work.charge(1, span(id)); }
std::optional<LayoutReader::Id> LayoutReader::first(Id id, K wanted) const {
  for (auto child : children(id))
    if (kind(child) == wanted)
      return child;
  return {};
}
Expected<ArrayRef<LayoutReader::Id>> LayoutReader::parts(Id id, size_t minimum,
                                                         size_t maximum) const {
  auto result = children(id);
  if (result.size() < minimum || result.size() > maximum)
    return fail(id, "layout node has an invalid child count");
  return result;
}
Expected<std::vector<StringRef>> LayoutReader::words(Id id) {
  const auto &node = tree.node(id);
  if (auto error = work.charge(node.lastToken - node.firstToken, span(id)))
    return error;
  std::vector<StringRef> result;
  for (auto token :
       tree.tokens().slice(node.firstToken, node.lastToken - node.firstToken))
    if (!token.trivia() && !token.synthetic())
      result.push_back(tree.text(token));
  return result;
}
Expected<std::string> LayoutReader::name(Id id) {
  auto tokens = words(id);
  if (!tokens)
    return tokens.takeError();
  std::string result;
  for (auto word : *tokens)
    result += word.str();
  return result;
}
StringRef LayoutReader::head(Id id) const {
  for (auto token :
       tree.tokens().slice(tree.node(id).firstToken,
                           tree.node(id).lastToken - tree.node(id).firstToken))
    if (!token.trivia() && !token.synthetic())
      return tree.text(token);
  return {};
}
bool LayoutReader::visible(Id id) const { return head(id) == "pub"; }
StringRef LayoutReader::between(Id left, Id right) const {
  for (uint32_t i = tree.node(left).lastToken; i < tree.node(right).firstToken;
       ++i) {
    auto token = tree.tokens()[i];
    if (!token.trivia() && !token.synthetic())
      return tree.text(token);
  }
  return {};
}
Error LayoutReader::runtimeArgument(Id id) const {
  if ((kind(id) == K::Argument || kind(id) == K::Parameter) &&
      head(id) == "ghost")
    return fail(id,
                "ghost arguments require the formal interface projection; they "
                "cannot bind runtime inputs",
                "source.assurance-unavailable");
  return Error::success();
}
Expected<LayoutReader::Id> LayoutReader::argument(Id id) const {
  if (kind(id) != K::Argument && kind(id) != K::Parameter)
    return id;
  if (auto error = runtimeArgument(id))
    return error;
  auto value = parts(id, 1, 1);
  if (!value)
    return value.takeError();
  return value->front();
}
Expected<std::vector<std::string>> LayoutReader::roles(Id id) {
  auto tokens = words(id);
  if (!tokens)
    return tokens.takeError();
  if (is_contained(*tokens, StringRef("->")))
    return fail(id,
                "holder-to-receiver roles require an oracle port; they are not "
                "shared availability",
                "source.oracle-unavailable");
  std::vector<std::string> result;
  for (auto child : children(id)) {
    if (kind(child) == K::Roles) {
      auto nested = roles(child);
      if (!nested)
        return nested.takeError();
      result.insert(result.end(), nested->begin(), nested->end());
    } else {
      auto value = argument(child);
      if (!value)
        return value.takeError();
      if (kind(*value) != K::Name)
        return fail(*value, "role must be a name", "source.roles");
      auto role = name(*value);
      if (!role)
        return role.takeError();
      result.push_back(std::move(*role));
    }
  }
  return result;
}
Expected<SyntaxType> LayoutReader::type(Id id) {
  if (auto error = charge(id))
    return error;
  SyntaxType value;
  value.span = span(id);
  auto nodes = children(id);
  switch (kind(id)) {
  case K::Argument:
  case K::Parameter: {
    auto inner = argument(id);
    if (!inner)
      return inner.takeError();
    return type(*inner);
  }
  case K::Name:
  case K::Literal: {
    auto spelling = name(id);
    if (!spelling)
      return spelling.takeError();
    value.name = std::move(*spelling);
    if (kind(id) == K::Literal) {
      value.kind = SyntaxType::Kind::Natural;
      if (tree.tokens()[tree.node(id).firstToken].kind !=
          syntax::TokenKind::Number)
        return fail(id, "expected a natural static argument");
    } else if (value.name == "_")
      value.kind = SyntaxType::Kind::Hole;
    break;
  }
  case K::Hole:
    value.kind = SyntaxType::Kind::Hole;
    break;
  case K::Group: {
    auto group = parts(id, 1, 1);
    if (!group)
      return group.takeError();
    auto inner = argument(group->front());
    if (!inner)
      return inner.takeError();
    auto projected = type(*inner);
    if (!projected)
      return projected.takeError();
    value = std::move(*projected);
    value.span = span(id);
    break;
  }
  case K::Tuple:
  case K::Array:
    value.kind = kind(id) == K::Tuple ? SyntaxType::Kind::Tuple
                                      : SyntaxType::Kind::Array;
    if (kind(id) == K::Array && nodes.size() != 2)
      return fail(id, "array type requires an element type and extent");
    for (auto node : nodes) {
      auto inner = argument(node);
      if (!inner)
        return inner.takeError();
      auto projected = type(*inner);
      if (!projected)
        return projected.takeError();
      value.arguments.push_back(std::move(*projected));
    }
    break;
  case K::StaticApply:
  case K::Projection:
  case K::Binary: {
    auto pair = parts(id, 2, 2);
    if (!pair)
      return pair.takeError();
    auto left = type((*pair)[0]);
    if (!left)
      return left.takeError();
    if (kind(id) == K::Binary) {
      auto symbol = between((*pair)[0], (*pair)[1]);
      if (symbol != "+" && symbol != "*")
        return fail(id,
                    "static arithmetic supports addition and multiplication");
      auto right = type((*pair)[1]);
      if (!right)
        return right.takeError();
      value.kind =
          symbol == "+" ? SyntaxType::Kind::Add : SyntaxType::Kind::Multiply;
      value.arguments = {std::move(*left), std::move(*right)};
    } else {
      value = std::move(*left);
      if (kind(id) == K::StaticApply) {
        if (auto error =
                staticArguments((*pair)[1], value.arguments, value.labels))
          return error;
      } else {
        auto member = name((*pair)[1]);
        if (!member)
          return member.takeError();
        value.name += "::" + *member;
      }
      value.span = span(id);
    }
    break;
  }
  case K::Call: {
    auto pair = parts(id, 2, 2);
    if (!pair)
      return pair.takeError();
    auto callee = name((*pair)[0]);
    if (!callee)
      return callee.takeError();
    if (*callee == "builtin" || *callee == "formal") {
      auto args = children((*pair)[1]);
      if (args.empty())
        return fail(id, "type constructor requires an identity string");
      auto identity = argument(args.front());
      if (!identity)
        return identity.takeError();
      auto spelling = tree.text(*identity);
      if (kind(*identity) != K::Literal || !spelling.starts_with('"') ||
          !spelling.ends_with('"'))
        return fail(*identity, "type constructor requires an identity string");
      value.kind = *callee == "builtin" ? SyntaxType::Kind::Builtin
                                        : SyntaxType::Kind::Formal;
      value.name = spelling.drop_front().drop_back().str();
      for (auto arg : args.drop_front()) {
        auto inner = argument(arg);
        if (!inner)
          return inner.takeError();
        auto projected = type(*inner);
        if (!projected)
          return projected.takeError();
        value.arguments.push_back(std::move(*projected));
      }
      break;
    }
    if (*callee != "pow2" || children((*pair)[1]).size() != 1)
      return fail(id, "unsupported static type constructor");
    auto inner = argument(children((*pair)[1])[0]);
    if (!inner)
      return inner.takeError();
    auto projected = type(*inner);
    if (!projected)
      return projected.takeError();
    value.kind = SyntaxType::Kind::PowerOfTwo;
    value.arguments.push_back(std::move(*projected));
    break;
  }
  default:
    return fail(id, "expected a native type or static argument");
  }
  for (const auto &child : value.arguments)
    value.height = std::max(value.height, child.height + 1);
  return value;
}
Error LayoutReader::staticArguments(Id id, std::vector<SyntaxType> &values,
                                    std::vector<ArgumentLabel> &labels) {
  for (auto arg : children(id)) {
    if (auto error = runtimeArgument(arg))
      return error;
    auto nodes = parts(arg, 1, 2);
    if (!nodes)
      return nodes.takeError();
    if (nodes->size() == 2) {
      auto label = name((*nodes)[0]);
      if (!label)
        return label.takeError();
      labels.push_back(
          {unsigned(values.size()), std::move(*label), span((*nodes)[0])});
    }
    auto value = type(nodes->back());
    if (!value)
      return value.takeError();
    values.push_back(std::move(*value));
  }
  return Error::success();
}
LayoutReader::LayoutReader(const syntax::Snapshot &tree, ArrayRef<Token> tokens,
                           Work &work)
    : tree(tree), work(work) {
  uint32_t significant = 0;
  for (const auto &token : tokens)
    if (token.kind != TokenKind::Whitespace && token.kind != TokenKind::Comment)
      writtenTokens.emplace(token.span.begin, significant++);
}
Error LayoutReader::bodies(ArrayRef<BodyParseScope> scopes,
                           std::vector<Diagnostic> *recovery) {
  std::map<uint32_t, Id> bodies, formalNodes;
  if (auto error = work.charge(tree.nodes().size()))
    return error;
  for (uint32_t i = 0; i < tree.nodes().size(); ++i) {
    Id id{i};
    if (syntax::category(kind(id)) == syntax::Category::Declaration)
      formalNodes.emplace(span(id).begin, id);
    if (kind(id) == K::Definition || kind(id) == K::Protocol ||
        kind(id) == K::Relation || kind(id) == K::OracleDefinition)
      if (auto suite = first(id, K::Suite))
        bodies.emplace(span(id).begin, *suite);
  }
  // The arena is built child-first. Mark malformed subtrees once, and use
  // diagnostic spans for insertion errors that need not own an Error child.
  std::vector<bool> malformed(tree.nodes().size());
  for (uint32_t i = 0; i < tree.nodes().size(); ++i) {
    Id id{i};
    if (auto error = work.charge(children(id).size()))
      return error;
    malformed[i] = syntax::category(kind(id)) == syntax::Category::Error;
    for (auto child : children(id))
      malformed[i] = malformed[i] || malformed[child.index];
  }
  auto invalid = [&](Id id) -> Expected<bool> {
    if (auto error = work.charge(tree.diagnostics().size() + 1, span(id)))
      return error;
    if (malformed[id.index])
      return true;
    auto extent = span(id);
    for (const auto &diagnostic : tree.diagnostics()) {
      if (!diagnostic.primary)
        return true;
      const auto at = *diagnostic.primary;
      if (at.source.index == extent.source.index && at.begin <= extent.end &&
          extent.begin <= at.end)
        return true;
    }
    return false;
  };
  auto record = [&](Error error) -> Error {
    if (!recovery)
      return error;
    auto diagnostic = diagnose(std::move(error));
    if (!diagnostic)
      return Error::success();
    if (diagnostic->code == "source.limit" ||
        diagnostic->code == "source.cancelled")
      return failure(diagnostic->code, diagnostic->message, diagnostic->primary,
                     diagnostic->related);
    recovery->push_back(std::move(*diagnostic));
    return Error::success();
  };
  for (const auto &item : scopes) {
    environment = item.environment;
    for (auto &formal : item.module->formalSyntax) {
      auto found = formalNodes.find(formal.tree.span(formal.node).begin);
      if (found == formalNodes.end())
        return failure("source.layout",
                       "formal source disappeared during parsing");
      formal.tree = tree;
      formal.node = found->second;
      auto malformed = invalid(formal.node);
      if (!malformed)
        return malformed.takeError();
      if (*malformed && recovery)
        continue;
      auto authored = readFormalSource(tree, formal.node, work);
      if (!authored) {
        if (auto error = record(authored.takeError()))
          return error;
        continue;
      }
      formal.authored = std::move(*authored);
    }
    for (auto &decl : item.module->members) {
      if (!decl.layoutSyntax || !decl.deferredBody)
        continue;
      auto found = bodies.find(decl.layoutDeclarationStart);
      if (found == bodies.end())
        return failure("source.layout",
                       "authored body disappeared during parsing", decl.span);
      auto malformed = invalid(found->second);
      if (!malformed)
        return malformed.takeError();
      if (*malformed && recovery) {
        decl.invalidBody = true;
        continue;
      }
      auto error = decl.kind == Declaration::Kind::Oracle
                       ? oracleDefinitionBody(found->second, decl)
                       : body(found->second, decl);
      if (error) {
        decl.invalidBody = true;
        if (auto fatal = record(std::move(error)))
          return fatal;
      }
    }
  }
  return Error::success();
}
} // namespace zkc::language::detail
