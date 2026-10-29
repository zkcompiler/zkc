#include "Internal.h"
#include "zkc/Language/Names.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language::detail {
namespace {
using K = syntax::Kind;
using Id = syntax::NodeId;
using Position = NotationDescriptor::Position;
using Association = NotationDescriptor::Association;

syntax::Budget budget(const Work &work) {
  syntax::Budget result;
  result.bytes = work.limits.fileBytes;
  result.tokens = work.limits.tokens;
  result.tokenBytes = work.limits.tokenBytes;
  result.identifierBytes = work.limits.identifierBytes;
  result.depth = work.limits.parseDepth;
  result.work = work.limits.work - work.used;
  return result;
}
Error acceptSnapshot(const syntax::Snapshot &tree, Work &work) {
  if (auto error = work.charge(tree.workUsed()))
    return error;
  if (tree.status() == syntax::Status::ResourceExhausted)
    return failure("source.limit", "layout parsing resource limit exceeded");
  if (!tree.diagnostics().empty()) {
    const auto &d = tree.diagnostics().front();
    return failure(d.code, d.message, d.primary, d.related);
  }
  if (tree.status() != syntax::Status::Complete)
    return failure("source.limit", "layout parsing did not complete");
  return Error::success();
}

/// The adapter consumes the immutable CST; it never prints or reparses another
/// language. All semantic decisions remain with the ordinary native checker.
class Adapter {
  const syntax::Snapshot &tree;
  Work &work;
  std::optional<Diagnostic> diagnostic;
  std::map<uint32_t, uint32_t> writtenTokens;
  std::optional<uint32_t> scope;
  std::shared_ptr<const NotationEnvironment> environment;
  std::vector<Id> attributes;

  ArrayRef<Id> children(Id id) const { return tree.children(id); }
  K kind(Id id) const { return tree.node(id).kind; }
  Span span(Id id) const { return tree.span(id); }
  bool fail(Id id, StringRef message, StringRef code = "source.layout") {
    if (!diagnostic)
      diagnostic = Diagnostic{code.str(), message.str(), span(id), {}};
    return false;
  }
  bool accept(Error error) {
    if (auto d = diagnose(std::move(error))) {
      if (!diagnostic)
        diagnostic = std::move(d);
      return false;
    }
    return !diagnostic;
  }
  bool charge(Id id) { return accept(work.charge(1, span(id))); }
  std::optional<Id> first(Id id, K wanted) const {
    for (auto child : children(id))
      if (kind(child) == wanted)
        return child;
    return {};
  }
  std::vector<StringRef> words(Id id) {
    const auto &node = tree.node(id);
    std::vector<StringRef> result;
    if (!accept(work.charge(node.lastToken - node.firstToken, span(id))))
      return result;
    for (auto token :
         tree.tokens().slice(node.firstToken, node.lastToken - node.firstToken))
      if (!token.trivia() && !token.synthetic())
        result.push_back(tree.text(token));
    return result;
  }
  std::string name(Id id) {
    std::string result;
    for (auto word : words(id))
      result += word.str();
    return result;
  }
  StringRef head(Id id) const {
    for (auto t : tree.tokens().slice(tree.node(id).firstToken,
                                      tree.node(id).lastToken -
                                          tree.node(id).firstToken))
      if (!t.trivia() && !t.synthetic())
        return tree.text(t);
    return {};
  }
  bool visible(Id id) const { return head(id) == "pub"; }
  StringRef between(Id left, Id right) const {
    for (uint32_t i = tree.node(left).lastToken;
         i < tree.node(right).firstToken; ++i) {
      auto token = tree.tokens()[i];
      if (!token.trivia() && !token.synthetic())
        return tree.text(token);
    }
    return {};
  }
  Id argument(Id id) {
    if (kind(id) != K::Argument && kind(id) != K::Parameter)
      return id;
    if (children(id).size() != 1)
      fail(id, "expected an unlabeled argument");
    return children(id).front();
  }
  std::vector<std::string> roles(Id id) {
    std::vector<std::string> result;
    for (auto child : children(id)) {
      if (kind(child) == K::Roles) {
        auto nested = roles(child);
        result.insert(result.end(), nested.begin(), nested.end());
      } else {
        child = argument(child);
        if (kind(child) != K::Name)
          fail(child, "role must be a name", "source.roles");
        result.push_back(name(child));
      }
    }
    return result;
  }
  SyntaxType type(Id id) {
    SyntaxType value;
    value.span = span(id);
    if (!charge(id))
      return value;
    auto parts = children(id);
    switch (kind(id)) {
    case K::Argument:
    case K::Parameter:
      return type(argument(id));
    case K::Name:
      value.name = name(id);
      if (value.name == "_")
        value.kind = SyntaxType::Kind::Hole;
      break;
    case K::Hole:
      value.kind = SyntaxType::Kind::Hole;
      break;
    case K::Literal:
      value.kind = SyntaxType::Kind::Natural;
      value.name = name(id);
      if (tree.tokens()[tree.node(id).firstToken].kind !=
          syntax::TokenKind::Number)
        fail(id, "expected a natural static argument");
      break;
    case K::Group:
      value = type(argument(parts.front()));
      value.span = span(id);
      break;
    case K::Tuple:
    case K::Array:
      value.kind = kind(id) == K::Tuple ? SyntaxType::Kind::Tuple
                                        : SyntaxType::Kind::Array;
      for (auto part : parts)
        value.arguments.push_back(type(argument(part)));
      if (kind(id) == K::Array && parts.size() != 2)
        fail(id, "array type requires an element type and extent");
      break;
    case K::StaticApply:
      value = type(parts[0]);
      staticArguments(parts[1], value.arguments, value.labels);
      value.span = span(id);
      break;
    case K::Projection:
      value = type(parts[0]);
      value.name += "::" + name(parts[1]);
      value.span = span(id);
      break;
    case K::Binary: {
      auto symbol = between(parts[0], parts[1]);
      if (symbol != "+" && symbol != "*")
        fail(id, "static arithmetic supports addition and multiplication");
      value.kind =
          symbol == "+" ? SyntaxType::Kind::Add : SyntaxType::Kind::Multiply;
      value.arguments = {type(parts[0]), type(parts[1])};
      break;
    }
    case K::Call:
      if (parts.size() == 2 && name(parts[0]) == "pow2" &&
          children(parts[1]).size() == 1) {
        value.kind = SyntaxType::Kind::PowerOfTwo;
        value.arguments.push_back(type(argument(children(parts[1])[0])));
      } else
        fail(id, "unsupported static type constructor");
      break;
    default:
      fail(id, "expected a native type or static argument");
    }
    for (const auto &child : value.arguments)
      value.height = std::max(value.height, child.height + 1);
    return value;
  }
  void staticArguments(Id id, std::vector<SyntaxType> &values,
                       std::vector<ArgumentLabel> &labels) {
    for (auto arg : children(id)) {
      auto parts = children(arg);
      if (parts.size() == 2) {
        labels.push_back(
            {unsigned(values.size()), name(parts[0]), span(parts[0])});
        values.push_back(type(parts[1]));
      } else
        values.push_back(type(argument(arg)));
    }
  }
  SyntaxPort port(Id id, bool unnamed = false) {
    SyntaxPort result;
    result.span = span(id);
    result.unnamed = unnamed;
    if (head(id) == "ghost") {
      fail(id, "ghost ports require the formal interface projection",
           "source.assurance-unavailable");
      return result;
    }
    Id target = id;
    if (!unnamed) {
      auto parts = children(id);
      if (parts.size() != 2 || kind(parts[0]) != K::Name) {
        fail(id, "native port requires a name and a type");
        return result;
      }
      result.name = name(parts[0]);
      target = parts[1];
    } else
      result.name = "result";
    if (kind(target) == K::RoleType) {
      auto parts = children(target);
      result.roles = roles(parts[1]);
      target = parts[0];
    }
    result.type = type(target);
    return result;
  }
  Id permissionBound(Id id, Permissions &permissions,
                     std::vector<std::string> &written) {
    if (kind(id) != K::Binary ||
        between(children(id)[0], children(id)[1]) != "+")
      return id;
    auto parts = children(id);
    auto base = permissionBound(parts[0], permissions, written);
    auto permission = name(parts[1]);
    if ((permission != "Copy" && permission != "Drop") ||
        is_contained(written, permission))
      fail(parts[1], "expected a distinct Copy or Drop bound",
           "source.permission");
    written.push_back(permission);
    permissions.copy |= permission == "Copy";
    permissions.drop |= permission == "Copy" || permission == "Drop";
    return base;
  }
  void parameters(Id id, SyntaxDeclaration &decl) {
    for (auto child : children(id)) {
      auto parts = children(child);
      if (parts.size() != 2 || kind(parts[0]) != K::Name) {
        fail(child, "static parameter requires a name and constraint");
        return;
      }
      SyntaxParameter parameter;
      parameter.name = name(parts[0]);
      parameter.constraint = type(permissionBound(
          parts[1], parameter.permissions, parameter.writtenPermissions));
      parameter.span = span(child);
      decl.parameters.push_back(std::move(parameter));
    }
  }
  bool requirements(Id id, SyntaxDeclaration &decl) {
    decl.explicitRequirements = true;
    std::function<bool(Id)> append = [&](Id value) {
      if (!charge(value))
        return false;
      if (kind(value) == K::Tuple || kind(value) == K::Group) {
        for (auto part : children(value))
          if (!append(argument(part)))
            return false;
        return true;
      }
      SyntaxRequirement requirement;
      requirement.span = span(value);
      auto parts = children(value);
      if (kind(value) == K::Binary && between(parts[0], parts[1]) == "<=") {
        requirement.lhs = type(parts[0]);
        requirement.rhs = type(parts[1]);
      } else if (kind(value) == K::Call && parts.size() == 2 &&
                 kind(parts[0]) == K::Name) {
        auto predicate = name(parts[0]);
        auto args = children(parts[1]);
        if (predicate == "Copy" || predicate == "Drop") {
          if (args.size() != 1)
            return fail(value, "permission requirement takes one type",
                        "source.permission");
          requirement.permission = predicate;
          requirement.lhs = type(argument(args[0]));
        } else {
          requirement.capability = predicate;
          for (auto arg : args)
            requirement.arguments.push_back(type(argument(arg)));
        }
      } else
        return fail(
            value,
            "expected a native natural, permission or capability requirement",
            "source.layout-unavailable");
      decl.requirements.push_back(std::move(requirement));
      return !diagnostic;
    };
    return append(children(id).front());
  }
  bool formal(Id id, SyntaxDeclaration &module) {
    if (kind(id) != K::Use &&
        !accept(work.count(work.declarations, work.limits.declarations,
                           "formal declaration count", span(id))))
      return false;
    FormalSyntax result{tree, id, {}, {}, visible(id)};
    if (kind(id) == K::Spec) {
      auto tokens = words(id);
      if (diagnostic)
        return false;
      bool named = tokens[visible(id) ? 2 : 1] != "for";
      auto parts = children(id);
      unsigned at = 0;
      if (named) {
        result.name = name(parts[at++]);
        if (kind(parts[at]) == K::StaticParameters)
          ++at;
      }
      result.subject = type(parts[at]);
      if (result.subject->kind != SyntaxType::Kind::Name)
        return fail(parts[at], "spec subject must name a protocol",
                    "source.spec.subject");
    }
    module.formalSyntax.push_back(std::move(result));
    return !diagnostic;
  }
  bool import(Id id, SyntaxDeclaration &module) {
    auto parts = children(id);
    auto tokens = words(id);
    if (diagnostic)
      return false;
    if (tokens.size() > (visible(id) ? 2u : 1u) &&
        tokens[visible(id) ? 2 : 1] == "lean")
      return formal(id, module);
    Import result;
    result.span = span(id);
    result.isPublic = visible(id);
    result.module = name(parts[0]);
    if (auto selected = first(id, K::Parameters)) {
      for (auto item : children(*selected)) {
        if (kind(item) != K::ImportSelector) {
          result.names.push_back(name(argument(item)));
          continue;
        }
        auto selector = words(item);
        if (diagnostic)
          return false;
        if (selector.front() == "indexing")
          result.indexing = true;
        else if (selector.front() == "operator")
          result.operators.push_back(selector[1].str());
        else if (selector.front() == "notation")
          result.notations.push_back(selector[1].str());
        else
          result.reductions.push_back(selector[1].str());
      }
    } else {
      result.alias = StringRef(result.module).rsplit("::").second.str();
      if (result.alias->empty())
        result.alias = result.module;
      if (parts.size() > 1) {
        result.alias = name(parts.back());
        result.explicitAlias = true;
      }
    }
    module.imports.push_back(std::move(result));
    return !diagnostic;
  }
  bool notation(Id id, SyntaxDeclaration &module) {
    auto tokens = words(id);
    auto parts = children(id);
    if (tokens.empty() || parts.empty())
      return false;
    size_t at = visible(id) ? 1 : 0;
    auto form = tokens[at++];
    SyntaxOperator result;
    result.span = span(id);
    result.isPublic = visible(id);
    auto descriptor = std::make_shared<NotationDescriptor>();
    if (form == "notation" || form == "indexing") {
      descriptor->position =
          form == "notation" ? Position::Delimited : Position::Index;
      descriptor->precedence = 100;
      descriptor->symbol = form == "notation" ? tokens[at].str() : "[]";
      for (auto hole : parts.drop_back())
        result.holes.push_back(name(hole));
      descriptor->arity = result.holes.size();
      if (form == "indexing")
        descriptor->closing = "]";
      else {
        auto assignment = llvm::find(tokens, StringRef("="));
        descriptor->closing = *(assignment - 1);
      }
      result.symbol = descriptor->symbol;
      result.notation = descriptor;
      result.explicitNotation = true;
      result.target = type(parts.back());
      module.operators.push_back(std::move(result));
      return !diagnostic;
    }
    if (form != "operator")
      return fail(id,
                  "native reduction projection requires scoped computations",
                  "source.layout-unavailable");
    auto fixity = tokens[at];
    if (fixity == "prefix" || fixity == "postfix" || fixity == "infix" ||
        fixity == "infixl" || fixity == "infixr") {
      descriptor->position = fixity == "prefix"    ? Position::Prefix
                             : fixity == "postfix" ? Position::Postfix
                                                   : Position::Infix;
      descriptor->association = fixity == "infixl"   ? Association::Left
                                : fixity == "infixr" ? Association::Right
                                                     : Association::None;
      descriptor->arity = descriptor->position == Position::Infix ? 2 : 1;
      tokens[at + 2].getAsInteger(10, descriptor->precedence);
      at += 4;
      result.explicitNotation = true;
    }
    result.symbol = tokens[at].str();
    descriptor->symbol = result.symbol;
    if (result.explicitNotation)
      result.notation = descriptor;
    result.target = type(parts.back());
    module.operators.push_back(std::move(result));
    return !diagnostic;
  }
  bool declaration(Id id, SyntaxDeclaration &parent) {
    if (!charge(id))
      return false;
    if (kind(id) == K::Attribute) {
      attributes.push_back(id);
      return true;
    }
    if (!attributes.empty() && kind(id) != K::TypeAlias &&
        kind(id) != K::Struct && kind(id) != K::Enum)
      return fail(attributes.front(),
                  "resource attributes must precede a type declaration",
                  "source.resource");
    if (kind(id) == K::Use)
      return import(id, parent);
    if (kind(id) == K::Notation)
      return notation(id, parent);
    StringRef mode;
    if (kind(id) == K::Definition) {
      auto tokens = words(id);
      if (diagnostic)
        return false;
      mode = tokens[visible(id) ? 1 : 0];
    }
    if (kind(id) == K::Spec || kind(id) == K::Relation || kind(id) == K::Law ||
        mode == "ghost")
      return formal(id, parent);
    SyntaxDeclaration result;
    result.layoutSyntax = true;
    result.span = span(id);
    result.explicitPublic = visible(id);
    result.isPublic =
        result.explicitPublic || parent.kind == Declaration::Kind::Interface;
    auto named = first(id, K::Name);
    if (!named && kind(id) != K::Section)
      return fail(id, "this declaration has no native execution projection",
                  "source.layout-unavailable");
    if (named)
      result.name = name(*named);
    using D = Declaration::Kind;
    switch (kind(id)) {
    case K::Section:
      if (result.explicitPublic)
        return fail(id, "section has no visibility boundary", "source.section");
      result.kind = D::Module;
      result.section = true;
      break;
    case K::Module:
      result.kind = D::Module;
      break;
    case K::Protocol:
      result.kind = D::Protocol;
      break;
    case K::Definition: {
      if (mode == "ghost")
        return fail(id,
                    "ghost definitions require the formal interface projection",
                    "source.assurance-unavailable");
      result.kind = mode == "local"   ? D::Local
                    : mode == "entry" ? D::EntryFunction
                                      : D::Math;
      break;
    }
    case K::TypeAlias:
      result.kind = D::Alias;
      break;
    case K::Domain:
      result.kind = D::Domain;
      break;
    case K::Struct:
      result.kind = D::Record;
      break;
    case K::Enum:
      result.kind = D::Variant;
      break;
    case K::Interface:
      result.kind = D::Interface;
      break;
    default:
      return fail(id, "this declaration has no native execution projection",
                  "source.layout-unavailable");
    }
    if (!accept(work.count(work.declarations, work.limits.declarations,
                           "declaration count", result.span)))
      return false;
    if (auto args = first(id, K::StaticParameters))
      parameters(*args, result);
    if (auto rs = first(id, K::Roles)) {
      if (result.kind != D::Protocol)
        return fail(*rs, "native role rosters belong to protocols",
                    "source.roles");
      result.roles = roles(*rs);
    }
    if (auto inputs = first(id, K::Parameters))
      for (auto input : children(*inputs)) {
        auto p = port(input);
        bool service =
            p.type.kind == SyntaxType::Kind::Name && p.type.name == "Random";
        auto &dest = service ? result.services : result.inputs;
        result.inputOrder.push_back({service
                                         ? Declaration::InputSlot::Kind::Service
                                         : Declaration::InputSlot::Kind::Data,
                                     unsigned(dest.size())});
        dest.push_back(std::move(p));
      }
    if (auto output = first(id, K::Result)) {
      auto value = children(*output).front();
      bool labeled = (kind(value) == K::Tuple || kind(value) == K::Group) &&
                     any_of(children(value), [&](Id item) {
                       return children(item).size() == 2;
                     });
      if (labeled)
        for (auto item : children(value))
          result.outputs.push_back(port(item));
      else
        result.outputs.push_back(port(value, true));
    }
    if (auto where = first(id, K::Where))
      if (!requirements(*where, result))
        return false;
    if (auto effects = first(id, K::Effects)) {
      if (result.kind != D::Math && result.kind != D::Local &&
          result.kind != D::EntryFunction && result.kind != D::Protocol)
        return fail(*effects, "native effect contracts belong to callables",
                    "source.effect");
      result.effects = Effects{};
      for (auto item : children(*effects)) {
        auto effect = name(argument(item));
        if (effect == "stop")
          result.effects->mayStop = true;
        else if (effect == "opaque")
          result.effects->opaque = true;
        else
          result.effectDependencies.push_back(std::move(effect));
      }
    }
    if (result.kind == D::Alias) {
      auto value = children(id).back();
      bool bound = between(*named, value) == ":";
      bool associated =
          bound || parent.kind == D::Interface || parent.definition.has_value();
      if (associated)
        result.kind = D::Associated;
      if (bound) {
        result.permissions.emplace();
        auto base = permissionBound(value, *result.permissions,
                                    result.writtenPermissions);
        auto sort = name(base);
        if (sort == "Copy" || sort == "Drop") {
          if (is_contained(result.writtenPermissions, sort))
            return fail(base, "duplicate associated permission",
                        "source.permission");
          result.writtenPermissions.insert(result.writtenPermissions.begin(),
                                           sort);
          result.permissions->copy |= sort == "Copy";
          result.permissions->drop = true;
        } else
          result.associatedSort = sort;
        if (parent.kind != D::Interface)
          return fail(id,
                      "an associated constraint without a representation "
                      "belongs to an interface",
                      "source.conformance");
        result.abstract = true;
      } else if (parent.kind == D::Interface)
        return fail(id, "an interface associated type requires a constraint",
                    "source.conformance");
      else
        result.definition = type(value);
    }
    if (result.kind == D::Module && !result.section)
      for (auto child : children(id))
        if (!(child == *named) &&
            syntax::category(kind(child)) == syntax::Category::Expression)
          result.definition = type(child);
    if (result.kind == D::Domain) {
      auto value = children(id).back();
      if (kind(value) != K::Call || children(value).size() != 2)
        return fail(value,
                    "domain requires an installed field or group constructor");
      auto args = children(children(value)[1]);
      if (args.size() != 1)
        return fail(value, "domain constructor requires one identity string");
      auto identity = argument(args.front());
      auto literal = tree.text(identity);
      if (kind(identity) != K::Literal || !literal.starts_with('"') ||
          !literal.ends_with('"'))
        return fail(identity, "domain identity must be a string");
      result.target = name(children(value)[0]);
      result.domain = literal.drop_front().drop_back().str();
    }
    if (!attributes.empty()) {
      result.span.begin = span(attributes.front()).begin;
      for (auto attribute : attributes) {
        auto parts = children(attribute);
        if (parts.size() != 1)
          return fail(attribute, "resource attribute takes no arguments",
                      "source.resource");
        auto name = this->name(parts.front());
        if (name == "affine" || name == "linear") {
          if (result.resource)
            return fail(attribute, "resource restriction was already specified",
                        "source.resource");
          result.resource =
              name == "affine" ? Resource::Affine : Resource::Linear;
        } else if (name == "sealed") {
          if (result.sealed)
            return fail(attribute, "constructor sealing was already specified",
                        "source.resource");
          result.sealed = true;
        } else
          return fail(attribute, "unknown native resource attribute",
                      "source.resource");
      }
      if (result.kind == D::Alias)
        result.kind = D::Associated;
      attributes.clear();
    }
    if (auto body = first(id, K::Suite)) {
      if (result.kind == D::Module || result.kind == D::Interface) {
        for (auto child : children(*body))
          if (!declaration(child, result))
            return false;
        if (!attributes.empty())
          return fail(attributes.front(),
                      "attribute has no following declaration",
                      "source.resource");
      } else if (result.kind == D::Record) {
        for (auto child : children(*body)) {
          auto field = port(child);
          field.isPublic = visible(child);
          result.fields.push_back(std::move(field));
        }
      } else if (result.kind == D::Variant) {
        for (auto child : children(*body)) {
          SyntaxAlternative alternative;
          alternative.name = name(children(child)[0]);
          alternative.span = span(child);
          if (auto fields = first(child, K::Parameters))
            for (auto field : children(*fields)) {
              auto value = port(argument(field), true);
              value.name = std::to_string(alternative.fields.size());
              alternative.fields.push_back(std::move(value));
            }
          result.alternatives.push_back(std::move(alternative));
        }
      } else
        return fail(*body, "unsupported declaration suite",
                    "source.layout-unavailable");
    } else if (first(id, K::OpaqueBody))
      result.deferredBody = DeferredBody{0, 0, 1, result.kind == D::Protocol};
    else if (result.kind == D::Module)
      result.externalModule = true;
    else if (result.kind == D::Math || result.kind == D::Local ||
             result.kind == D::Protocol) {
      if (parent.kind != D::Interface)
        return fail(id, "a bodyless signature belongs to an interface",
                    "source.conformance");
      result.abstract = true;
    }
    parent.members.push_back(std::move(result));
    return !diagnostic;
  }

  Pattern pattern(Id id) {
    Pattern result;
    result.span = span(id);
    if (!charge(id))
      return result;
    switch (kind(id)) {
    case K::Name:
      result.name = name(id);
      if (result.name == "_")
        result.kind = Pattern::Kind::Ignore;
      if (auto token = writtenTokens.find(span(id).begin);
          token != writtenTokens.end())
        result.writtenToken = token->second;
      break;
    case K::Group:
      return pattern(argument(children(id)[0]));
    case K::Tuple:
      result.kind =
          children(id).empty() ? Pattern::Kind::Unit : Pattern::Kind::Tuple;
      for (auto child : children(id))
        result.children.push_back(pattern(argument(child)));
      break;
    case K::Record: {
      auto parts = children(id);
      result.kind = Pattern::Kind::Record;
      result.type = type(parts[0]);
      result.name = result.type->name;
      for (auto field : children(parts[1])) {
        auto values = children(field);
        result.labels.push_back(name(values[0]));
        result.shorthand.push_back(values.size() == 1);
        result.children.push_back(pattern(values.back()));
      }
      break;
    }
    default:
      fail(id, "unsupported native binding pattern");
    }
    return result;
  }
  std::shared_ptr<const NotationDescriptor> descriptor(Id id, StringRef symbol,
                                                       Position position) {
    NotationDescriptor key;
    key.symbol = symbol.str();
    key.position = position;
    if (!accept(work.charge(symbol.size() + 13, span(id))))
      return {};
    auto found = environment->find(key.key());
    if (found != environment->end())
      return found->second.descriptor;
    fail(id, "operator has no visible syntax binding",
         "source.notation-visibility");
    return {};
  }
  uint32_t expression(Id id, SyntaxDeclaration &decl) {
    Expression result;
    result.kind = Expression::Kind::Name;
    result.span = span(id);
    result.scope = scope;
    if (!charge(id))
      return 0;
    auto parts = children(id);
    switch (kind(id)) {
    case K::Argument:
      return expression(argument(id), decl);
    case K::Name:
      result.text = name(id);
      break;
    case K::Literal:
      result.text = name(id);
      result.kind = result.text == "true" || result.text == "false"
                        ? Expression::Kind::Boolean
                        : Expression::Kind::Decimal;
      if (StringRef(result.text).starts_with('"'))
        fail(id, "string is not an executable value");
      break;
    case K::Group: {
      auto inner = expression(argument(parts[0]), decl);
      if (!diagnostic) {
        decl.expressions[inner].grouped = true;
        decl.expressions[inner].span = span(id);
      }
      return inner;
    }
    case K::RoleType:
      result.children.push_back(expression(parts[0], decl));
      if (!diagnostic) {
        auto index = result.children[0];
        decl.expressions[index].roles = roles(parts[1]);
        decl.expressions[index].span = span(id);
        return index;
      }
      break;
    case K::Tuple:
    case K::Array:
      result.kind = kind(id) == K::Tuple ? Expression::Kind::Tuple
                                         : Expression::Kind::Array;
      for (auto part : parts)
        result.children.push_back(expression(argument(part), decl));
      break;
    case K::Projection:
      result.kind = Expression::Kind::Projection;
      result.text = name(parts[1]);
      result.children.push_back(expression(parts[0], decl));
      break;
    case K::Index: {
      result.kind = Expression::Kind::Subscript;
      result.bracket = true;
      result.children.push_back(expression(parts[0], decl));
      for (auto item : children(parts[1]))
        result.children.push_back(expression(argument(item), decl));
      auto descriptor = std::make_shared<NotationDescriptor>();
      descriptor->position = Position::Index;
      descriptor->symbol = "[]";
      descriptor->closing = "]";
      descriptor->precedence = 100;
      descriptor->arity = result.children.size();
      result.notation = std::move(descriptor);
      break;
    }
    case K::Record: {
      result.kind = Expression::Kind::Record;
      auto target = type(parts[0]);
      result.text = target.name;
      result.arguments = std::move(target.arguments);
      result.staticLabels = std::move(target.labels);
      for (auto field : children(parts[1])) {
        auto values = children(field);
        result.labels.push_back(name(values[0]));
        auto value = expression(values.back(), decl);
        if (values.size() == 1 && !diagnostic)
          decl.expressions[value].shorthand = true;
        result.children.push_back(value);
      }
      break;
    }
    case K::StaticApply:
      result.text = name(parts[0]);
      staticArguments(parts[1], result.arguments, result.staticLabels);
      break;
    case K::If:
    case K::Match:
    case K::For: {
      result.kind = kind(id) == K::If      ? Expression::Kind::If
                    : kind(id) == K::Match ? Expression::Kind::Match
                                           : Expression::Kind::For;
      auto region = [&](Id suite) {
        auto index = uint32_t(decl.bodies.size());
        if (body(suite, decl, true))
          result.regions.push_back(index);
      };
      if (kind(id) == K::For) {
        result.index = pattern(parts[0]);
        result.children = {expression(parts[1], decl),
                           expression(parts[2], decl)};
        for (auto part : parts.drop_front(3))
          if (kind(part) == K::Roles)
            result.roles = roles(part);
          else if (kind(part) != K::Suite)
            result.arguments.push_back(type(part));
        region(parts.back());
      } else {
        result.children.push_back(expression(parts[0], decl));
        if (kind(id) == K::If) {
          region(parts[1]);
          if (parts.size() == 3)
            region(children(parts[2])[0]);
          else {
            SyntaxBody empty;
            empty.span = span(id);
            empty.region = true;
            empty.parent = scope;
            empty.notationEnvironment = environment;
            result.regions.push_back(decl.bodies.size());
            decl.bodies.push_back(std::move(empty));
          }
        } else {
          for (auto arm : children(parts[1])) {
            auto match = children(arm)[0];
            std::vector<Pattern> payload;
            if (kind(match) == K::Call) {
              for (auto arg : children(children(match)[1]))
                payload.push_back(pattern(argument(arg)));
              match = children(match)[0];
            }
            if (kind(match) != K::Name)
              fail(match, "match arm requires a variant constructor",
                   "source.match");
            auto label = name(match);
            if (StringRef(label).contains("::"))
              fail(match,
                   "qualified match patterns are not implemented; use the "
                   "bare alternative checked against the scrutinee type",
                   "source.layout-unavailable");
            result.labels.push_back(std::move(label));
            result.payloads.push_back(std::move(payload));
            region(children(arm)[1]);
          }
        }
      }
      break;
    }
    case K::Delimited:
      result.kind = Expression::Kind::NotationCall;
      result.text = head(id).str();
      result.notation = descriptor(id, result.text, Position::Delimited);
      for (auto part : parts)
        result.children.push_back(expression(part, decl));
      break;
    case K::Call: {
      if (parts.size() == 1) {
        result.kind = Expression::Kind::NotationCall;
        auto tokens = words(id);
        if (diagnostic)
          return 0;
        result.text = tokens.back().str();
        result.notation = descriptor(id, result.text, Position::Postfix);
        result.children.push_back(expression(parts.front(), decl));
        break;
      }
      auto callee = parts[0];
      if (kind(callee) == K::StaticApply) {
        staticArguments(children(callee)[1], result.arguments,
                        result.staticLabels);
        callee = children(callee)[0];
      }
      if (kind(callee) == K::Projection &&
          between(children(callee)[0], children(callee)[1]) == ".") {
        result.kind = Expression::Kind::MethodCall;
        result.text = name(children(callee)[1]);
        result.children.push_back(expression(children(callee)[0], decl));
      } else if (kind(callee) == K::Name || kind(callee) == K::Projection) {
        result.kind = Expression::Kind::Call;
        auto target = type(callee);
        result.text = std::move(target.name);
        if (!target.arguments.empty()) {
          auto offset = target.arguments.size();
          target.arguments.insert(target.arguments.end(),
                                  result.arguments.begin(),
                                  result.arguments.end());
          result.arguments = std::move(target.arguments);
          for (auto &label : result.staticLabels)
            label.index += offset;
          result.staticLabels.insert(result.staticLabels.begin(),
                                     target.labels.begin(),
                                     target.labels.end());
        }
      } else {
        fail(callee, "expected a named native callable");
        break;
      }
      for (auto arg : children(parts[1])) {
        auto values = children(arg);
        if (values.size() == 2) {
          result.callLabels.push_back({unsigned(result.children.size()),
                                       name(values[0]), span(values[0])});
          result.children.push_back(expression(values[1], decl));
        } else
          result.children.push_back(expression(argument(arg), decl));
      }
      break;
    }
    case K::Binary:
    case K::Prefix: {
      auto symbol =
          kind(id) == K::Binary ? between(parts[0], parts[1]) : head(id);
      result.kind = symbol == "and" || symbol == "∧" || symbol == "&&"
                        ? Expression::Kind::And
                    : symbol == "or" || symbol == "∨" || symbol == "||"
                        ? Expression::Kind::Or
                    : symbol == "not" || symbol == "¬" || symbol == "!"
                        ? Expression::Kind::Not
                        : Expression::Kind::NotationCall;
      if (result.kind == Expression::Kind::NotationCall)
        result.notation = descriptor(id, symbol,
                                     kind(id) == K::Binary ? Position::Infix
                                                           : Position::Prefix);
      for (auto part : parts)
        result.children.push_back(expression(part, decl));
      break;
    }
    default:
      fail(id, "this expression has no native layout execution projection",
           "source.layout-unavailable");
    }
    if (diagnostic)
      return 0;
    for (auto child : result.children)
      result.height =
          std::max(result.height, decl.expressions[child].height + 1);
    auto index = uint32_t(decl.expressions.size());
    decl.expressions.push_back(std::move(result));
    return index;
  }
  bool body(Id id, SyntaxDeclaration &decl, bool region = false) {
    SyntaxBody result;
    result.span = span(id);
    result.notationEnvironment = environment;
    result.parent = scope;
    result.region = region;
    auto previousScope = scope;
    auto restore = scope_exit([&] { scope = previousScope; });
    auto bodyIndex = uint32_t(decl.bodies.size());
    scope = bodyIndex;
    decl.bodies.emplace_back();
    std::optional<std::string> site;
    std::optional<Span> attributeSpan;
    for (auto item : children(id)) {
      if (result.returned)
        return fail(item, "statement follows the return", "source.return");
      if (!charge(item))
        return false;
      auto parts = children(item);
      if (kind(item) == K::Attribute) {
        if (site || parts.size() != 2 || name(parts[0]) != "site" ||
            children(parts[1]).size() != 1)
          return fail(item, "expected one site label for the following action",
                      "source.site");
        auto label = argument(children(parts[1])[0]);
        if (kind(label) != K::Name)
          return fail(label, "site label must be a name", "source.site");
        site = name(label);
        attributeSpan = span(item);
        continue;
      }
      if (kind(item) == K::Return) {
        if (region)
          return fail(item, "nested suites use a final expression",
                      "source.return");
        if (site)
          return fail(item, "site label cannot select return", "source.site");
        auto value = parts[0];
        result.returned = true;
        if (decl.kind == Declaration::Kind::Protocol &&
            (kind(value) == K::Tuple || kind(value) == K::Group) &&
            any_of(children(value),
                   [&](Id child) { return children(child).size() == 2; })) {
          for (auto child : children(value)) {
            auto entry = children(child);
            if (entry.size() != 2)
              return fail(child, "named return requires every output name",
                          "source.return");
            result.results.emplace_back(name(entry[0]),
                                        expression(entry[1], decl));
          }
        } else
          result.results.emplace_back(
              decl.kind == Declaration::Kind::Protocol ? "" : "result",
              expression(value, decl));
        continue;
      }
      Statement statement;
      statement.span = span(item);
      statement.site = std::move(site);
      site.reset();
      if (attributeSpan)
        statement.span.begin = attributeSpan->begin;
      attributeSpan.reset();
      statement.evaluation = Statement::Evaluation::Pure;
      if (parts.empty())
        return fail(item, "empty executable statement");
      auto value = parts.back();
      switch (kind(item)) {
      case K::Binding:
      case K::ActionBinding:
      case K::Update:
        statement.kind = kind(item) == K::Update ? Statement::Kind::Assign
                                                 : Statement::Kind::Let;
        statement.mutableBinding = head(item) == "mut";
        statement.pattern = pattern(parts[0]);
        if (parts.size() == 3) {
          auto annotation = parts[1];
          if (kind(annotation) == K::RoleType) {
            statement.roles = roles(children(annotation)[1]);
            annotation = children(annotation)[0];
          }
          statement.type = type(annotation);
        }
        if (kind(item) == K::ActionBinding)
          statement.evaluation = Statement::Evaluation::Ordered;
        if (kind(value) == K::Send) {
          auto send = children(value);
          bool explicitSender = between(send[0], send[1]) == "from";
          if (send.size() != (explicitSender ? 3 : 2))
            return fail(value, "multiple-recipient send is not implemented yet",
                        "source.layout-unavailable");
          statement.exchange =
              std::make_pair(explicitSender ? name(send[1]) : std::string{},
                             name(send.back()));
          value = send[0];
        }
        break;
      case K::Guard:
        statement.kind = Statement::Kind::Require;
        if (parts.size() == 2) {
          auto owners = roles(parts[0]);
          if (owners.size() != 1)
            return fail(item, "guard needs one owner", "source.roles");
          statement.owner = owners[0];
        }
        break;
      case K::ExpressionStatement:
        statement.kind = Statement::Kind::Expression;
        if ((region || decl.kind == Declaration::Kind::Math) &&
            item == children(id).back()) {
          if (statement.site)
            return fail(item, "site label cannot select an implicit result",
                        "source.site");
          result.returned = !region;
          result.implicitResult = !region;
          result.results.emplace_back("result", expression(value, decl));
          continue;
        }
        break;
      case K::If:
      case K::Match:
      case K::For:
        statement.kind = Statement::Kind::Expression;
        statement.terminated = false;
        value = item;
        break;
      default:
        return fail(item,
                    "this statement has no native layout execution projection",
                    "source.layout-unavailable");
      }
      statement.expression = expression(value, decl);
      result.statements.push_back(std::move(statement));
      if (diagnostic)
        return false;
    }
    if (site)
      return fail(id, "site label needs a following action", "source.site");
    decl.bodies[bodyIndex] = std::move(result);
    if (!region)
      decl.deferredBody.reset();
    return !diagnostic;
  }

public:
  Adapter(const syntax::Snapshot &tree, ArrayRef<Token> tokens, Work &work)
      : tree(tree), work(work) {
    uint32_t significant = 0;
    for (const auto &token : tokens)
      if (token.kind != TokenKind::Whitespace &&
          token.kind != TokenKind::Comment) {
        writtenTokens.emplace(token.span.begin, significant++);
      }
  }
  Expected<SyntaxDeclaration> headers() {
    SyntaxDeclaration root;
    root.kind = Declaration::Kind::Module;
    root.layoutSyntax = true;
    root.name = tree.revision().buffer().module;
    root.span = {tree.sourceId(), 0, uint32_t(tree.revision().text().size())};
    root.isPublic = true;
    if (!accept(work.count(work.declarations, work.limits.declarations,
                           "module count", root.span)))
      return takeError();
    bool firstItem = true;
    for (auto item : children(tree.root())) {
      if (firstItem && kind(item) == K::Module && !first(item, K::Suite)) {
        auto moduleName = first(item, K::Name);
        auto declaredName = moduleName ? name(*moduleName) : std::string{};
        if (diagnostic)
          return takeError();
        if (!moduleName || declaredName != root.name)
          return failure("source.module",
                         "file module name differs from captured module",
                         span(item));
        root.explicitPublic = visible(item);
        if (auto args = first(item, K::StaticParameters))
          parameters(*args, root);
        if (auto where = first(item, K::Where))
          if (!requirements(*where, root))
            return takeError();
        if (first(item, K::Roles))
          return failure("source.roles", "a module has no runtime role roster",
                         span(item));
        if (auto effects = first(item, K::Effects))
          return failure("source.effect",
                         "native effect contracts belong to callables",
                         span(*effects));
        for (auto child : children(item))
          if (!(child == *moduleName) &&
              syntax::category(kind(child)) == syntax::Category::Expression)
            root.definition = type(child);
      } else if (!declaration(item, root))
        return takeError();
      firstItem = false;
    }
    if (!attributes.empty())
      fail(attributes.front(), "attribute has no following declaration",
           "source.resource");
    if (diagnostic)
      return takeError();
    return root;
  }
  Error takeError() {
    if (diagnostic)
      return failure(diagnostic->code, diagnostic->message, diagnostic->primary,
                     diagnostic->related);
    return failure("source.layout", "layout adaptation did not complete");
  }
  Error bodies(ArrayRef<BodyParseScope> scopes) {
    std::map<uint32_t, Id> bodies, formalNodes;
    if (!accept(work.charge(tree.nodes().size())))
      return takeError();
    for (uint32_t i = 0; i < tree.nodes().size(); ++i) {
      Id id{i};
      if (syntax::category(kind(id)) == syntax::Category::Declaration)
        formalNodes.emplace(span(id).begin, id);
      if (kind(id) == K::Definition || kind(id) == K::Protocol ||
          kind(id) == K::Relation)
        if (auto suite = first(id, K::Suite))
          bodies.emplace(span(id).begin, *suite);
    }
    for (const auto &item : scopes) {
      environment = item.environment;
      for (auto &formal : item.module->formalSyntax) {
        auto found = formalNodes.find(formal.tree.span(formal.node).begin);
        if (found == formalNodes.end())
          return failure("source.layout",
                         "formal source disappeared during parsing");
        formal.tree = tree;
        formal.node = found->second;
      }
      for (auto &decl : item.module->members) {
        if (!decl.layoutSyntax || !decl.deferredBody)
          continue;
        auto found = bodies.find(decl.span.begin);
        if (found == bodies.end())
          return failure("source.layout",
                         "authored body disappeared during parsing", decl.span);
        if (!body(found->second, decl))
          return takeError();
      }
    }
    return Error::success();
  }
};
} // namespace

Error expandLayoutSections(std::vector<SyntaxDeclaration> &modules,
                           Work &work) {
  std::function<Error(SyntaxDeclaration &, ArrayRef<SyntaxParameter>,
                      std::vector<SyntaxDeclaration> &)>
      expand;
  expand = [&](SyntaxDeclaration &source, ArrayRef<SyntaxParameter> inherited,
               std::vector<SyntaxDeclaration> &output) -> Error {
    if (auto error = work.charge(
            inherited.size() + source.parameters.size() + 1, source.span))
      return error;
    std::function<Error(const SyntaxType &)> chargeType =
        [&](const SyntaxType &type) -> Error {
      if (auto error =
              work.charge(type.name.size() + type.labels.size() + 1, type.span))
        return error;
      for (const auto &argument : type.arguments)
        if (auto error = chargeType(argument))
          return error;
      return Error::success();
    };
    for (const auto &parameter : inherited)
      if (auto error = chargeType(parameter.constraint))
        return error;
    if (source.section) {
      if (!source.imports.empty() || !source.operators.empty())
        return failure("source.section",
                       "section groups declarations; put imports and notation "
                       "in the enclosing module",
                       source.span);
      std::vector<SyntaxParameter> parameters(inherited.begin(),
                                              inherited.end());
      parameters.insert(parameters.end(), source.parameters.begin(),
                        source.parameters.end());
      for (auto &child : source.members)
        if (auto error = expand(child, parameters, output))
          return error;
    } else {
      source.parameters.insert(source.parameters.begin(), inherited.begin(),
                               inherited.end());
      std::vector<SyntaxDeclaration> members;
      for (auto &child : source.members) {
        if (child.section) {
          std::function<void(SyntaxDeclaration &)> moveFormal =
              [&](SyntaxDeclaration &group) {
                for (auto &formal : group.formalSyntax)
                  source.formalSyntax.push_back(std::move(formal));
                group.formalSyntax.clear();
                for (auto &nested : group.members)
                  if (nested.section)
                    moveFormal(nested);
              };
          moveFormal(child);
        }
        if (auto error = expand(child, {}, members))
          return error;
      }
      source.members = std::move(members);
      output.push_back(std::move(source));
    }
    return Error::success();
  };
  std::vector<SyntaxDeclaration> expanded;
  for (auto &module : modules)
    if (auto error = expand(module, {}, expanded))
      return error;
  modules = std::move(expanded);
  return Error::success();
}

Expected<SyntaxDeclaration> parseLayoutHeaders(const SourceBuffer &source,
                                               SourceId id,
                                               CheckedStorage &storage,
                                               Work &work) {
  auto tree = syntax::parseHeaders(source::Revision(source), id, budget(work));
  if (auto error = acceptSnapshot(tree, work))
    return std::move(error);
  auto &tokens = storage.tokens[id.index];
  for (auto token : tree.tokens()) {
    if (token.synthetic() && token.kind != syntax::TokenKind::End)
      continue;
    TokenKind kind;
    switch (token.kind) {
    case syntax::TokenKind::Word:
      kind = TokenKind::Word;
      break;
    case syntax::TokenKind::Number:
      kind = TokenKind::Decimal;
      break;
    case syntax::TokenKind::String:
      kind = TokenKind::String;
      break;
    case syntax::TokenKind::Comment:
      kind = TokenKind::Comment;
      break;
    case syntax::TokenKind::Space:
    case syntax::TokenKind::Newline:
      kind = TokenKind::Whitespace;
      break;
    case syntax::TokenKind::End:
      kind = TokenKind::End;
      break;
    default:
      kind = TokenKind::Punctuation;
      break;
    }
    Span span{id, token.begin, token.end};
    if (auto error =
            work.count(work.tokens, work.limits.tokens, "token count", span))
      return std::move(error);
    tokens.push_back({kind, span});
  }
  storage.layoutHeaders[id.index] = tree;
  return Adapter(tree, tokens, work).headers();
}
Error parseLayoutBodies(SourceId id, ArrayRef<BodyParseScope> scopes,
                        CheckedStorage &storage, Work &work) {
  syntax::Environments environments;
  syntax::Environment defaults;
  for (const auto &scope : scopes) {
    syntax::Environment environment;
    for (const auto &[_, item] : *scope.environment)
      environment.notation.push_back(*item.descriptor);
    if (scope.module->span.begin == 0 &&
        scope.module->name == (*storage.sources)[id.index].module)
      defaults = std::move(environment);
    else
      environments.emplace(scope.module->span.begin, std::move(environment));
  }
  auto tree =
      syntax::parseBodies(*storage.layoutHeaders[id.index], std::move(defaults),
                          std::move(environments), budget(work));
  if (auto error = acceptSnapshot(tree, work))
    return error;
  storage.layoutBodies[id.index] = tree;
  return Adapter(tree, storage.tokens[id.index], work).bodies(scopes);
}
} // namespace zkc::language::detail
