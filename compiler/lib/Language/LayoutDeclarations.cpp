#include "LayoutReader.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
Expected<SyntaxPort> LayoutReader::port(Id id, bool unnamed) {
  SyntaxPort result;
  result.span = span(id);
  result.unnamed = unnamed;
  if (auto error = runtimeArgument(id))
    return error;
  if (head(id) == "ghost")
    return fail(id, "ghost ports require the formal interface projection",
                "source.assurance-unavailable");
  Id target = id;
  if (!unnamed) {
    auto projected2 = parts(id, 2, 2);
    if (!projected2)
      return projected2.takeError();
    auto nodes = std::move(*projected2);
    if (kind(nodes[0]) != K::Name)
      return fail(id, "native port requires a name and a type");
    auto projected3 = name(nodes[0]);
    if (!projected3)
      return projected3.takeError();
    result.name = std::move(*projected3);
    target = nodes[1];
  } else
    result.name = "result";
  if (kind(target) == K::RoleType) {
    auto projected4 = parts(target, 2, 2);
    if (!projected4)
      return projected4.takeError();
    auto nodes = std::move(*projected4);
    auto roleNodes = children(nodes[1]);
    bool custody =
        roleNodes.size() >= 2 && between(roleNodes[0], roleNodes[1]) == "->";
    if (custody) {
      auto holder = name(roleNodes.front());
      if (!holder)
        return holder.takeError();
      result.oracleHolder = std::move(*holder);
      for (auto receiver : roleNodes.drop_front()) {
        if (kind(receiver) != K::Name)
          return fail(receiver, "oracle receiver must be a role name",
                      "source.oracle-port");
        auto value = name(receiver);
        if (!value)
          return value.takeError();
        result.roles.push_back(std::move(*value));
      }
    } else {
      auto projected = roles(nodes[1]);
      if (!projected)
        return projected.takeError();
      result.roles = std::move(*projected);
    }
    target = nodes[0];
  }
  auto projected6 = type(target);
  if (!projected6)
    return projected6.takeError();
  result.type = std::move(*projected6);
  return result;
}
Expected<LayoutReader::Id>
LayoutReader::permissionBound(Id id, Permissions &permissions,
                              std::vector<std::string> &written) {
  if (kind(id) != K::Binary)
    return id;
  auto projected7 = parts(id, 2, 2);
  if (!projected7)
    return projected7.takeError();
  auto nodes = std::move(*projected7);
  if (between(nodes[0], nodes[1]) != "+")
    return id;
  auto projected8 = permissionBound(nodes[0], permissions, written);
  if (!projected8)
    return projected8.takeError();
  auto base = std::move(*projected8);
  auto projected9 = name(nodes[1]);
  if (!projected9)
    return projected9.takeError();
  auto permission = std::move(*projected9);
  if ((permission != "Copy" && permission != "Drop") ||
      is_contained(written, permission))
    return fail(nodes[1], "expected a distinct Copy or Drop bound",
                "source.permission");
  written.push_back(permission);
  permissions.copy |= permission == "Copy";
  permissions.drop |= permission == "Copy" || permission == "Drop";
  return base;
}
Error LayoutReader::parameters(Id id, SyntaxDeclaration &decl) {
  for (auto child : children(id)) {
    auto projected10 = parts(child, 2, 2);
    if (!projected10)
      return projected10.takeError();
    auto nodes = std::move(*projected10);
    if (kind(nodes[0]) != K::Name)
      return fail(child, "static parameter requires a name and constraint");
    SyntaxParameter parameter;
    auto projected11 = name(nodes[0]);
    if (!projected11)
      return projected11.takeError();
    parameter.name = std::move(*projected11);
    auto projected12 = permissionBound(nodes[1], parameter.permissions,
                                       parameter.writtenPermissions);
    if (!projected12)
      return projected12.takeError();
    auto bound = std::move(*projected12);
    auto projected13 = type(bound);
    if (!projected13)
      return projected13.takeError();
    parameter.constraint = std::move(*projected13);
    parameter.span = span(child);
    decl.parameters.push_back(std::move(parameter));
  }
  return Error::success();
}
Error LayoutReader::requirements(Id id, SyntaxDeclaration &decl) {
  decl.explicitRequirements = true;
  std::function<Error(Id)> append = [&](Id value) -> Error {
    if (auto error = charge(value))
      return error;
    if (kind(value) == K::Tuple || kind(value) == K::Group) {
      for (auto part : children(value)) {
        auto projected15 = argument(part);
        if (!projected15)
          return projected15.takeError();
        auto inner = std::move(*projected15);
        if (auto error = append(inner))
          return error;
      }
      return Error::success();
    }
    SyntaxRequirement requirement;
    requirement.span = span(value);
    auto nodes = children(value);
    if (kind(value) == K::Binary && nodes.size() == 2 &&
        between(nodes[0], nodes[1]) == "<=") {
      auto projected17 = type(nodes[0]);
      if (!projected17)
        return projected17.takeError();
      requirement.lhs = std::move(*projected17);
      auto projected18 = type(nodes[1]);
      if (!projected18)
        return projected18.takeError();
      requirement.rhs = std::move(*projected18);
    } else if (kind(value) == K::Call && nodes.size() == 2 &&
               kind(nodes[0]) == K::Name) {
      auto projected19 = name(nodes[0]);
      if (!projected19)
        return projected19.takeError();
      auto predicate = std::move(*projected19);
      auto args = children(nodes[1]);
      if (predicate == "Copy" || predicate == "Drop") {
        if (args.size() != 1)
          return fail(value, "permission requirement takes one type",
                      "source.permission");
        requirement.permission = predicate;
        auto projected20 = argument(args[0]);
        if (!projected20)
          return projected20.takeError();
        auto inner = std::move(*projected20);
        auto projected21 = type(inner);
        if (!projected21)
          return projected21.takeError();
        requirement.lhs = std::move(*projected21);
      } else {
        requirement.capability = predicate;
        for (auto arg : args) {
          auto projected22 = argument(arg);
          if (!projected22)
            return projected22.takeError();
          auto inner = std::move(*projected22);
          auto projected23 = type(inner);
          if (!projected23)
            return projected23.takeError();
          auto projected = std::move(*projected23);
          requirement.arguments.push_back(std::move(projected));
        }
      }
    } else
      return fail(
          value,
          "expected a native natural, permission or capability requirement",
          "source.layout-unavailable");
    decl.requirements.push_back(std::move(requirement));
    return Error::success();
  };
  auto projected24 = parts(id, 1, 1);
  if (!projected24)
    return projected24.takeError();
  auto nodes = std::move(*projected24);
  return append(nodes.front());
}
Error LayoutReader::formal(Id id, SyntaxDeclaration &module) {
  if (kind(id) != K::Use) {
    if (auto error = work.count(work.declarations, work.limits.declarations,
                                "formal declaration count", span(id)))
      return error;
  }
  FormalSyntax result{tree, id, {}, {}, visible(id), {}};
  if (kind(id) == K::Spec) {
    auto projected26 = words(id);
    if (!projected26)
      return projected26.takeError();
    auto tokens = std::move(*projected26);
    size_t namePosition = visible(id) ? 2 : 1;
    if (tokens.size() <= namePosition)
      return fail(id, "spec requires a subject", "source.spec.subject");
    bool named = tokens[namePosition] != "for";
    auto nodes = children(id);
    unsigned at = 0;
    if (named) {
      if (nodes.empty())
        return fail(id, "named spec requires a name", "source.spec.name");
      auto projected27 = name(nodes[at++]);
      if (!projected27)
        return projected27.takeError();
      result.name = std::move(*projected27);
      if (at < nodes.size() && kind(nodes[at]) == K::StaticParameters)
        ++at;
    }
    if (at >= nodes.size())
      return fail(id, "spec requires a subject", "source.spec.subject");
    auto projected28 = type(nodes[at]);
    if (!projected28)
      return projected28.takeError();
    result.subject = std::move(*projected28);
    if (result.subject->kind != SyntaxType::Kind::Name)
      return fail(nodes[at], "spec subject must name a protocol",
                  "source.spec.subject");
  }
  module.formalSyntax.push_back(std::move(result));
  return Error::success();
}
Error LayoutReader::import(Id id, SyntaxDeclaration &module) {
  auto projected29 = parts(id, 1, 3);
  if (!projected29)
    return projected29.takeError();
  auto nodes = std::move(*projected29);
  auto projected30 = words(id);
  if (!projected30)
    return projected30.takeError();
  auto tokens = std::move(*projected30);
  if (tokens.size() > (visible(id) ? 2u : 1u) &&
      tokens[visible(id) ? 2 : 1] == "lean")
    return formal(id, module);
  Import result;
  result.span = span(id);
  result.isPublic = visible(id);
  auto projected31 = name(nodes[0]);
  if (!projected31)
    return projected31.takeError();
  result.module = std::move(*projected31);
  if (auto selected = first(id, K::Parameters)) {
    for (auto item : children(*selected)) {
      if (kind(item) != K::ImportSelector) {
        auto projected32 = argument(item);
        if (!projected32)
          return projected32.takeError();
        auto inner = std::move(*projected32);
        auto projected33 = name(inner);
        if (!projected33)
          return projected33.takeError();
        auto selectedName = std::move(*projected33);
        result.names.push_back(std::move(selectedName));
        continue;
      }
      auto projected34 = words(item);
      if (!projected34)
        return projected34.takeError();
      auto selector = std::move(*projected34);
      if (selector.empty())
        return fail(item, "empty import selector");
      if (selector.front() == "indexing")
        result.indexing = true;
      else {
        if (selector.size() != 2)
          return fail(item, "import selector requires a symbol");
        if (selector.front() == "operator")
          result.operators.push_back(selector[1].str());
        else if (selector.front() == "notation")
          result.notations.push_back(selector[1].str());
        else
          result.reductions.push_back(selector[1].str());
      }
    }
  } else {
    result.alias = StringRef(result.module).rsplit("::").second.str();
    if (result.alias->empty())
      result.alias = result.module;
    if (nodes.size() > 1) {
      auto projected35 = name(nodes.back());
      if (!projected35)
        return projected35.takeError();
      result.alias = std::move(*projected35);
      result.explicitAlias = true;
    }
  }
  module.imports.push_back(std::move(result));
  return Error::success();
}
Error LayoutReader::notation(Id id, SyntaxDeclaration &module) {
  auto projected36 = words(id);
  if (!projected36)
    return projected36.takeError();
  auto tokens = std::move(*projected36);
  auto nodes = children(id);
  size_t at = visible(id) ? 1 : 0;
  if (tokens.size() <= at + 1 || nodes.empty())
    return fail(id, "incomplete notation declaration");
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
    for (auto hole : nodes.drop_back()) {
      auto projected37 = name(hole);
      if (!projected37)
        return projected37.takeError();
      auto holeName = std::move(*projected37);
      result.holes.push_back(std::move(holeName));
    }
    descriptor->arity = result.holes.size();
    if (form == "indexing")
      descriptor->closing = "]";
    else {
      auto assignment = llvm::find(tokens, StringRef("="));
      if (assignment == tokens.begin() || assignment == tokens.end())
        return fail(id, "notation requires a closing delimiter and target");
      descriptor->closing = *(assignment - 1);
    }
    result.symbol = descriptor->symbol;
    result.notation = descriptor;
    result.explicitNotation = true;
  } else {
    if (form != "operator")
      return fail(id,
                  "native reduction projection requires scoped computations",
                  "source.layout-unavailable");
    auto fixity = tokens[at];
    if (fixity == "prefix" || fixity == "postfix" || fixity == "infix" ||
        fixity == "infixl" || fixity == "infixr") {
      if (tokens.size() <= at + 4 ||
          tokens[at + 2].getAsInteger(10, descriptor->precedence))
        return fail(id, "operator requires a numeric precedence and symbol");
      descriptor->position = fixity == "prefix"    ? Position::Prefix
                             : fixity == "postfix" ? Position::Postfix
                                                   : Position::Infix;
      descriptor->association = fixity == "infixl"   ? Association::Left
                                : fixity == "infixr" ? Association::Right
                                                     : Association::None;
      descriptor->arity = descriptor->position == Position::Infix ? 2 : 1;
      at += 4;
      result.explicitNotation = true;
    }
    result.symbol = tokens[at].str();
    descriptor->symbol = result.symbol;
    if (result.explicitNotation)
      result.notation = descriptor;
  }
  auto projected38 = type(nodes.back());
  if (!projected38)
    return projected38.takeError();
  result.target = std::move(*projected38);
  module.operators.push_back(std::move(result));
  return Error::success();
}
Error LayoutReader::declaration(Id id, SyntaxDeclaration &parent) {
  if (auto error = charge(id))
    return error;
  if (kind(id) == K::Attribute) {
    attributes.push_back(id);
    return Error::success();
  }
  if (!attributes.empty() && kind(id) != K::TypeAlias &&
      kind(id) != K::Struct && kind(id) != K::Enum && kind(id) != K::Protocol)
    return fail(attributes.front(),
                "resource attributes must precede a type declaration",
                "source.resource");
  if (kind(id) == K::Use)
    return import(id, parent);
  if (kind(id) == K::Notation)
    return notation(id, parent);
  StringRef mode;
  if (kind(id) == K::Definition) {
    auto projected40 = words(id);
    if (!projected40)
      return projected40.takeError();
    auto tokens = std::move(*projected40);
    size_t at = visible(id) ? 1 : 0;
    if (tokens.size() <= at)
      return fail(id, "incomplete definition");
    mode = tokens[at];
  }
  if (kind(id) == K::Spec || kind(id) == K::Relation || kind(id) == K::Law ||
      mode == "ghost")
    return formal(id, parent);
  SyntaxDeclaration result;
  result.layoutSyntax = true;
  result.span = span(id);
  result.layoutDeclarationStart = span(id).begin;
  result.explicitPublic = visible(id);
  result.isPublic =
      result.explicitPublic || parent.kind == Declaration::Kind::Interface;
  auto named = first(id, K::Name);
  if (!named && kind(id) != K::Section)
    return fail(id, "this declaration has no native execution projection",
                "source.layout-unavailable");
  if (named) {
    auto projected41 = name(*named);
    if (!projected41)
      return projected41.takeError();
    result.name = std::move(*projected41);
  }
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
  case K::Definition:
    result.kind = mode == "local"   ? D::Local
                  : mode == "entry" ? D::EntryFunction
                                    : D::Math;
    break;
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
  if (auto error = work.count(work.declarations, work.limits.declarations,
                              "declaration count", result.span))
    return error;
  if (auto args = first(id, K::StaticParameters)) {
    if (auto error = parameters(*args, result))
      return error;
  }
  if (auto roster = first(id, K::Roles)) {
    if (result.kind != D::Protocol)
      return fail(*roster, "native role rosters belong to protocols",
                  "source.roles");
    auto projected44 = roles(*roster);
    if (!projected44)
      return projected44.takeError();
    result.roles = std::move(*projected44);
  }
  if (auto inputs = first(id, K::Parameters)) {
    for (auto input : children(*inputs)) {
      auto projected45 = port(input);
      if (!projected45)
        return projected45.takeError();
      auto value = std::move(*projected45);
      result.inputOrder.push_back(
          {Declaration::InputSlot::Kind::Data, unsigned(result.inputs.size())});
      result.inputs.push_back(std::move(value));
    }
  }
  if (auto output = first(id, K::Result)) {
    auto projected46 = parts(*output, 1, 1);
    if (!projected46)
      return projected46.takeError();
    auto nodes = std::move(*projected46);
    auto value = nodes.front();
    bool labeled = (kind(value) == K::Tuple || kind(value) == K::Group) &&
                   any_of(children(value),
                          [&](Id item) { return children(item).size() == 2; });
    if (labeled) {
      for (auto item : children(value)) {
        auto projected47 = port(item);
        if (!projected47)
          return projected47.takeError();
        auto projected = std::move(*projected47);
        result.outputs.push_back(std::move(projected));
      }
    } else {
      auto projected48 = port(value, true);
      if (!projected48)
        return projected48.takeError();
      auto projected = std::move(*projected48);
      result.outputs.push_back(std::move(projected));
    }
  }
  if (auto where = first(id, K::Where)) {
    if (auto error = requirements(*where, result))
      return error;
  }
  if (auto effects = first(id, K::Effects)) {
    if (result.kind != D::Math && result.kind != D::Local &&
        result.kind != D::EntryFunction && result.kind != D::Protocol)
      return fail(*effects, "native effect contracts belong to callables",
                  "source.effect");
    result.effects = Effects{};
    for (auto item : children(*effects)) {
      auto projected50 = argument(item);
      if (!projected50)
        return projected50.takeError();
      auto inner = std::move(*projected50);
      auto projected51 = name(inner);
      if (!projected51)
        return projected51.takeError();
      auto effect = std::move(*projected51);
      if (effect == "stop")
        result.effects->mayStop = true;
      else if (effect == "opaque")
        result.effects->opaque = true;
      else
        result.effectDependencies.push_back(std::move(effect));
    }
  }
  if (result.kind == D::Alias) {
    auto projected52 = parts(id, 2, SIZE_MAX);
    if (!projected52)
      return projected52.takeError();
    auto nodes = std::move(*projected52);
    auto value = nodes.back();
    bool bound = between(*named, value) == ":";
    if (bound || parent.kind == D::Interface || parent.definition.has_value())
      result.kind = D::Associated;
    if (bound) {
      result.permissions.emplace();
      auto projected53 = permissionBound(value, *result.permissions,
                                         result.writtenPermissions);
      if (!projected53)
        return projected53.takeError();
      auto base = std::move(*projected53);
      auto projected54 = name(base);
      if (!projected54)
        return projected54.takeError();
      auto sort = std::move(*projected54);
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
                    "an associated constraint without a representation belongs "
                    "to an interface",
                    "source.conformance");
      result.abstract = true;
    } else if (parent.kind == D::Interface)
      return fail(id, "an interface associated type requires a constraint",
                  "source.conformance");
    else {
      auto projected55 = type(value);
      if (!projected55)
        return projected55.takeError();
      result.definition = std::move(*projected55);
    }
  }
  if (result.kind == D::Module && !result.section) {
    for (auto child : children(id)) {
      if (!(child == *named) &&
          syntax::category(kind(child)) == syntax::Category::Expression) {
        auto projected56 = type(child);
        if (!projected56)
          return projected56.takeError();
        result.definition = std::move(*projected56);
      }
    }
  }
  if (result.kind == D::Domain) {
    auto projected57 = parts(id, 2, SIZE_MAX);
    if (!projected57)
      return projected57.takeError();
    auto nodes = std::move(*projected57);
    auto value = nodes.back();
    if (kind(value) != K::Call)
      return fail(value,
                  "domain requires an installed field or group constructor");
    auto projected58 = parts(value, 2, 2);
    if (!projected58)
      return projected58.takeError();
    auto call = std::move(*projected58);
    auto projected59 = parts(call[1], 1, 1);
    if (!projected59)
      return projected59.takeError();
    auto args = std::move(*projected59);
    auto projected60 = argument(args.front());
    if (!projected60)
      return projected60.takeError();
    auto identity = std::move(*projected60);
    auto literal = tree.text(identity);
    if (kind(identity) != K::Literal || !literal.starts_with('"') ||
        !literal.ends_with('"'))
      return fail(identity, "domain identity must be a string");
    auto projected61 = name(call[0]);
    if (!projected61)
      return projected61.takeError();
    result.target = std::move(*projected61);
    result.domain = literal.drop_front().drop_back().str();
  }
  if (!attributes.empty() && result.kind == D::Protocol) {
    result.span.begin = span(attributes.front()).begin;
    if (auto error = oracleShapes(result))
      return error;
    attributes.clear();
  }
  if (!attributes.empty()) {
    result.span.begin = span(attributes.front()).begin;
    for (auto attribute : attributes) {
      auto projected62 = parts(attribute, 1, 1);
      if (!projected62)
        return projected62.takeError();
      auto nodes = std::move(*projected62);
      auto projected63 = name(nodes.front());
      if (!projected63)
        return projected63.takeError();
      auto attributeName = std::move(*projected63);
      if (attributeName == "affine" || attributeName == "linear") {
        if (result.resource)
          return fail(attribute, "resource restriction was already specified",
                      "source.resource");
        result.resource =
            attributeName == "affine" ? Resource::Affine : Resource::Linear;
      } else if (attributeName == "sealed") {
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
  if (auto suite = first(id, K::Suite)) {
    if (result.kind == D::Module || result.kind == D::Interface) {
      for (auto child : children(*suite)) {
        if (auto error = declaration(child, result))
          return error;
      }
      if (!attributes.empty())
        return fail(attributes.front(),
                    "attribute has no following declaration",
                    "source.resource");
    } else if (result.kind == D::Record) {
      for (auto child : children(*suite)) {
        auto projected65 = port(child);
        if (!projected65)
          return projected65.takeError();
        auto field = std::move(*projected65);
        field.isPublic = visible(child);
        result.fields.push_back(std::move(field));
      }
    } else if (result.kind == D::Variant) {
      for (auto child : children(*suite)) {
        auto projected66 = parts(child, 1, 2);
        if (!projected66)
          return projected66.takeError();
        auto nodes = std::move(*projected66);
        SyntaxAlternative alternative;
        auto projected67 = name(nodes[0]);
        if (!projected67)
          return projected67.takeError();
        alternative.name = std::move(*projected67);
        alternative.span = span(child);
        if (auto fields = first(child, K::Parameters)) {
          for (auto field : children(*fields)) {
            auto projected68 = argument(field);
            if (!projected68)
              return projected68.takeError();
            auto inner = std::move(*projected68);
            auto projected69 = port(inner, true);
            if (!projected69)
              return projected69.takeError();
            auto value = std::move(*projected69);
            value.name = std::to_string(alternative.fields.size());
            alternative.fields.push_back(std::move(value));
          }
        }
        result.alternatives.push_back(std::move(alternative));
      }
    } else
      return fail(*suite, "unsupported declaration suite",
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
  return Error::success();
}
Expected<SyntaxDeclaration> LayoutReader::headers() {
  SyntaxDeclaration root;
  root.kind = Declaration::Kind::Module;
  root.layoutSyntax = true;
  root.name = tree.revision().buffer().module;
  root.span = {tree.sourceId(), 0, uint32_t(tree.revision().text().size())};
  root.isPublic = true;
  if (auto error = work.count(work.declarations, work.limits.declarations,
                              "module count", root.span))
    return error;
  bool firstItem = true;
  for (auto item : children(tree.root())) {
    if (firstItem && kind(item) == K::Module && !first(item, K::Suite)) {
      auto moduleName = first(item, K::Name);
      if (!moduleName)
        return fail(item, "file module needs a name", "source.module");
      auto projected71 = name(*moduleName);
      if (!projected71)
        return projected71.takeError();
      auto declaredName = std::move(*projected71);
      if (declaredName != root.name)
        return fail(item, "file module name differs from captured module",
                    "source.module");
      root.explicitPublic = visible(item);
      if (auto args = first(item, K::StaticParameters)) {
        if (auto error = parameters(*args, root))
          return error;
      }
      if (auto where = first(item, K::Where)) {
        if (auto error = requirements(*where, root))
          return error;
      }
      if (first(item, K::Roles))
        return fail(item, "a module has no runtime role roster",
                    "source.roles");
      if (auto effects = first(item, K::Effects))
        return fail(*effects, "native effect contracts belong to callables",
                    "source.effect");
      for (auto child : children(item)) {
        if (!(child == *moduleName) &&
            syntax::category(kind(child)) == syntax::Category::Expression) {
          auto projected74 = type(child);
          if (!projected74)
            return projected74.takeError();
          root.definition = std::move(*projected74);
        }
      }
    } else {
      if (auto error = declaration(item, root))
        return error;
    }
    firstItem = false;
  }
  if (!attributes.empty())
    return fail(attributes.front(), "attribute has no following declaration",
                "source.resource");
  return root;
}
} // namespace zkc::language::detail
