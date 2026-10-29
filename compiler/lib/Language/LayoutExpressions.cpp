#include "LayoutReader.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
Expected<Pattern> LayoutReader::pattern(Id id) {
  if (auto error = charge(id))
    return error;
  Pattern result;
  result.span = span(id);
  switch (kind(id)) {
  case K::Name: {
    auto projected2 = name(id);
    if (!projected2)
      return projected2.takeError();
    result.name = std::move(*projected2);
    if (result.name == "_")
      result.kind = Pattern::Kind::Ignore;
    if (auto token = writtenTokens.find(span(id).begin);
        token != writtenTokens.end())
      result.writtenToken = token->second;
    break;
  }
  case K::Group: {
    auto projected3 = parts(id, 1, 1);
    if (!projected3)
      return projected3.takeError();
    auto nodes = std::move(*projected3);
    auto projected4 = argument(nodes[0]);
    if (!projected4)
      return projected4.takeError();
    auto inner = std::move(*projected4);
    return pattern(inner);
  }
  case K::Tuple:
    result.kind =
        children(id).empty() ? Pattern::Kind::Unit : Pattern::Kind::Tuple;
    for (auto child : children(id)) {
      auto projected5 = argument(child);
      if (!projected5)
        return projected5.takeError();
      auto inner = std::move(*projected5);
      auto projected6 = pattern(inner);
      if (!projected6)
        return projected6.takeError();
      auto projected = std::move(*projected6);
      result.children.push_back(std::move(projected));
    }
    break;
  case K::Record: {
    auto projected7 = parts(id, 2, 2);
    if (!projected7)
      return projected7.takeError();
    auto nodes = std::move(*projected7);
    result.kind = Pattern::Kind::Record;
    auto projected8 = type(nodes[0]);
    if (!projected8)
      return projected8.takeError();
    result.type = std::move(*projected8);
    result.name = result.type->name;
    for (auto field : children(nodes[1])) {
      auto projected9 = parts(field, 1, 2);
      if (!projected9)
        return projected9.takeError();
      auto values = std::move(*projected9);
      auto projected10 = name(values[0]);
      if (!projected10)
        return projected10.takeError();
      auto label = std::move(*projected10);
      result.labels.push_back(std::move(label));
      result.shorthand.push_back(values.size() == 1);
      auto projected11 = pattern(values.back());
      if (!projected11)
        return projected11.takeError();
      auto projected = std::move(*projected11);
      result.children.push_back(std::move(projected));
    }
    break;
  }
  default:
    return fail(id, "unsupported native binding pattern");
  }
  return result;
}
Expected<std::shared_ptr<const NotationDescriptor>>
LayoutReader::descriptor(Id id, StringRef symbol, Position position) {
  if (auto error = work.charge(symbol.size() + 13, span(id)))
    return error;
  if (!environment)
    return fail(id, "expression has no notation environment",
                "source.notation-visibility");
  NotationDescriptor key;
  key.symbol = symbol.str();
  key.position = position;
  auto found = environment->find(key.key());
  if (found == environment->end())
    return fail(id, "operator has no visible syntax binding",
                "source.notation-visibility");
  return found->second.descriptor;
}
Expected<uint32_t> LayoutReader::expression(Id id, SyntaxDeclaration &decl) {
  if (auto error = charge(id))
    return error;
  Expression result;
  result.kind = Expression::Kind::Name;
  result.span = span(id);
  result.scope = scope;
  auto nodes = children(id);
  auto append = [&](Id child) -> Error {
    auto projected14 = expression(child, decl);
    if (!projected14)
      return projected14.takeError();
    auto projected = std::move(*projected14);
    result.children.push_back(projected);
    return Error::success();
  };
  switch (kind(id)) {
  case K::Argument: {
    auto projected15 = argument(id);
    if (!projected15)
      return projected15.takeError();
    auto inner = std::move(*projected15);
    return expression(inner, decl);
  }
  case K::Name: {
    auto projected16 = name(id);
    if (!projected16)
      return projected16.takeError();
    result.text = std::move(*projected16);
    break;
  }
  case K::Literal: {
    auto projected17 = name(id);
    if (!projected17)
      return projected17.takeError();
    result.text = std::move(*projected17);
    result.kind = result.text == "true" || result.text == "false"
                      ? Expression::Kind::Boolean
                      : Expression::Kind::Decimal;
    if (StringRef(result.text).starts_with('"'))
      return fail(id, "string is not an executable value");
    break;
  }
  case K::Group: {
    auto projected18 = parts(id, 1, 1);
    if (!projected18)
      return projected18.takeError();
    auto group = std::move(*projected18);
    auto projected19 = argument(group[0]);
    if (!projected19)
      return projected19.takeError();
    auto inner = std::move(*projected19);
    auto projected20 = expression(inner, decl);
    if (!projected20)
      return projected20.takeError();
    auto index = std::move(*projected20);
    decl.expressions[index].grouped = true;
    decl.expressions[index].span = span(id);
    return index;
  }
  case K::RoleType: {
    auto projected21 = parts(id, 2, 2);
    if (!projected21)
      return projected21.takeError();
    auto pair = std::move(*projected21);
    auto projected22 = roles(pair[1]);
    if (!projected22)
      return projected22.takeError();
    auto availability = std::move(*projected22);
    auto projected23 = expression(pair[0], decl);
    if (!projected23)
      return projected23.takeError();
    auto index = std::move(*projected23);
    decl.expressions[index].roles = std::move(availability);
    decl.expressions[index].span = span(id);
    return index;
  }
  case K::Tuple:
  case K::Array:
    result.kind = kind(id) == K::Tuple ? Expression::Kind::Tuple
                                       : Expression::Kind::Array;
    for (auto node : nodes) {
      auto projected24 = argument(node);
      if (!projected24)
        return projected24.takeError();
      auto inner = std::move(*projected24);
      if (auto error = append(inner))
        return error;
    }
    break;
  case K::Projection: {
    auto projected26 = parts(id, 2, 2);
    if (!projected26)
      return projected26.takeError();
    auto pair = std::move(*projected26);
    result.kind = Expression::Kind::Projection;
    auto projected27 = name(pair[1]);
    if (!projected27)
      return projected27.takeError();
    result.text = std::move(*projected27);
    if (auto error = append(pair[0]))
      return error;
    break;
  }
  case K::Index: {
    auto projected29 = parts(id, 2, 2);
    if (!projected29)
      return projected29.takeError();
    auto pair = std::move(*projected29);
    result.kind = Expression::Kind::Subscript;
    result.bracket = true;
    if (auto error = append(pair[0]))
      return error;
    for (auto item : children(pair[1])) {
      auto projected31 = argument(item);
      if (!projected31)
        return projected31.takeError();
      auto inner = std::move(*projected31);
      if (auto error = append(inner))
        return error;
    }
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
    auto projected33 = parts(id, 2, 2);
    if (!projected33)
      return projected33.takeError();
    auto pair = std::move(*projected33);
    auto projected34 = type(pair[0]);
    if (!projected34)
      return projected34.takeError();
    auto target = std::move(*projected34);
    result.kind = Expression::Kind::Record;
    result.text = target.name;
    result.arguments = std::move(target.arguments);
    result.staticLabels = std::move(target.labels);
    for (auto field : children(pair[1])) {
      if (auto error = runtimeArgument(field))
        return error;
      auto projected36 = parts(field, 1, 2);
      if (!projected36)
        return projected36.takeError();
      auto values = std::move(*projected36);
      auto projected37 = name(values[0]);
      if (!projected37)
        return projected37.takeError();
      auto label = std::move(*projected37);
      result.labels.push_back(std::move(label));
      auto projected38 = expression(values.back(), decl);
      if (!projected38)
        return projected38.takeError();
      auto value = std::move(*projected38);
      if (values.size() == 1)
        decl.expressions[value].shorthand = true;
      result.children.push_back(value);
    }
    break;
  }
  case K::StaticApply: {
    auto projected39 = parts(id, 2, 2);
    if (!projected39)
      return projected39.takeError();
    auto pair = std::move(*projected39);
    auto projected40 = name(pair[0]);
    if (!projected40)
      return projected40.takeError();
    result.text = std::move(*projected40);
    if (auto error =
            staticArguments(pair[1], result.arguments, result.staticLabels))
      return error;
    break;
  }
  case K::If:
  case K::Match:
  case K::For: {
    result.kind = kind(id) == K::If      ? Expression::Kind::If
                  : kind(id) == K::Match ? Expression::Kind::Match
                                         : Expression::Kind::For;
    auto region = [&](Id suite) -> Error {
      auto index = uint32_t(decl.bodies.size());
      if (auto error = body(suite, decl, true))
        return error;
      result.regions.push_back(index);
      return Error::success();
    };
    if (kind(id) == K::For) {
      auto projected43 = parts(id, 4, SIZE_MAX);
      if (!projected43)
        return projected43.takeError();
      auto loop = std::move(*projected43);
      auto projected44 = pattern(loop[0]);
      if (!projected44)
        return projected44.takeError();
      result.index = std::move(*projected44);
      if (auto error = append(loop[1]))
        return error;
      if (auto error = append(loop[2]))
        return error;
      for (auto part : loop.drop_front(3)) {
        if (kind(part) == K::Roles) {
          auto projected47 = roles(part);
          if (!projected47)
            return projected47.takeError();
          result.roles = std::move(*projected47);
        } else if (kind(part) != K::Suite) {
          auto projected48 = type(part);
          if (!projected48)
            return projected48.takeError();
          auto bound = std::move(*projected48);
          result.arguments.push_back(std::move(bound));
        }
      }
      if (auto error = region(loop.back()))
        return error;
    } else {
      auto projected50 = parts(id, 2, 3);
      if (!projected50)
        return projected50.takeError();
      auto control = std::move(*projected50);
      if (auto error = append(control[0]))
        return error;
      if (kind(id) == K::If) {
        if (auto error = region(control[1]))
          return error;
        if (control.size() == 3) {
          auto projected53 = parts(control[2], 1, 1);
          if (!projected53)
            return projected53.takeError();
          auto alternative = std::move(*projected53);
          if (auto error = region(alternative[0]))
            return error;
        } else {
          SyntaxBody empty;
          empty.span = span(id);
          empty.region = true;
          empty.parent = scope;
          empty.notationEnvironment = environment;
          result.regions.push_back(decl.bodies.size());
          decl.bodies.push_back(std::move(empty));
        }
      } else {
        for (auto arm : children(control[1])) {
          auto projected55 = parts(arm, 2, 2);
          if (!projected55)
            return projected55.takeError();
          auto armNodes = std::move(*projected55);
          auto match = armNodes[0];
          std::vector<Pattern> payload;
          if (kind(match) == K::Call) {
            auto projected56 = parts(match, 2, 2);
            if (!projected56)
              return projected56.takeError();
            auto call = std::move(*projected56);
            for (auto arg : children(call[1])) {
              auto projected57 = argument(arg);
              if (!projected57)
                return projected57.takeError();
              auto inner = std::move(*projected57);
              auto projected58 = pattern(inner);
              if (!projected58)
                return projected58.takeError();
              auto projected = std::move(*projected58);
              payload.push_back(std::move(projected));
            }
            match = call[0];
          }
          if (kind(match) != K::Name)
            return fail(match, "match arm requires a variant constructor",
                        "source.match");
          auto projected59 = name(match);
          if (!projected59)
            return projected59.takeError();
          auto label = std::move(*projected59);
          result.labels.push_back(std::move(label));
          result.constructorSpans.push_back(span(match));
          result.payloads.push_back(std::move(payload));
          if (auto error = region(armNodes[1]))
            return error;
        }
      }
    }
    break;
  }
  case K::Delimited: {
    result.kind = Expression::Kind::NotationCall;
    result.text = head(id).str();
    auto projected61 = descriptor(id, result.text, Position::Delimited);
    if (!projected61)
      return projected61.takeError();
    result.notation = std::move(*projected61);
    for (auto part : nodes) {
      if (auto error = append(part))
        return error;
    }
    break;
  }
  case K::Call: {
    auto projected63 = parts(id, 1, 2);
    if (!projected63)
      return projected63.takeError();
    auto call = std::move(*projected63);
    if (call.size() == 1) {
      result.kind = Expression::Kind::NotationCall;
      auto projected64 = words(id);
      if (!projected64)
        return projected64.takeError();
      auto tokens = std::move(*projected64);
      if (tokens.empty())
        return fail(id, "empty postfix call");
      result.text = tokens.back().str();
      auto projected65 = descriptor(id, result.text, Position::Postfix);
      if (!projected65)
        return projected65.takeError();
      result.notation = std::move(*projected65);
      if (auto error = append(call.front()))
        return error;
      break;
    }
    auto callee = call[0];
    if (kind(callee) == K::StaticApply) {
      auto projected67 = parts(callee, 2, 2);
      if (!projected67)
        return projected67.takeError();
      auto application = std::move(*projected67);
      if (auto error = staticArguments(application[1], result.arguments,
                                       result.staticLabels))
        return error;
      callee = application[0];
    }
    auto calleeNodes = children(callee);
    if (kind(callee) == K::Projection && calleeNodes.size() == 2 &&
        between(calleeNodes[0], calleeNodes[1]) == ".") {
      result.kind = Expression::Kind::MethodCall;
      auto projected69 = name(calleeNodes[1]);
      if (!projected69)
        return projected69.takeError();
      result.text = std::move(*projected69);
      if (auto error = append(calleeNodes[0]))
        return error;
    } else if (kind(callee) == K::Name || kind(callee) == K::Projection) {
      result.kind = Expression::Kind::Call;
      auto projected71 = type(callee);
      if (!projected71)
        return projected71.takeError();
      auto target = std::move(*projected71);
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
                                   target.labels.begin(), target.labels.end());
      }
    } else
      return fail(callee, "expected a named native callable");
    for (auto arg : children(call[1])) {
      if (auto error = runtimeArgument(arg))
        return error;
      auto projected73 = parts(arg, 1, 2);
      if (!projected73)
        return projected73.takeError();
      auto values = std::move(*projected73);
      if (values.size() == 2) {
        auto projected74 = name(values[0]);
        if (!projected74)
          return projected74.takeError();
        auto label = std::move(*projected74);
        result.callLabels.push_back({unsigned(result.children.size()),
                                     std::move(label), span(values[0])});
      }
      if (auto error = append(values.back()))
        return error;
    }
    break;
  }
  case K::Binary:
  case K::Prefix: {
    auto projected76 =
        parts(id, kind(id) == K::Binary ? 2 : 1, kind(id) == K::Binary ? 2 : 1);
    if (!projected76)
      return projected76.takeError();
    auto operands = std::move(*projected76);
    auto symbol =
        kind(id) == K::Binary ? between(operands[0], operands[1]) : head(id);
    result.kind = symbol == "and" || symbol == "∧" || symbol == "&&"
                      ? Expression::Kind::And
                  : symbol == "or" || symbol == "∨" || symbol == "||"
                      ? Expression::Kind::Or
                  : symbol == "not" || symbol == "¬" || symbol == "!"
                      ? Expression::Kind::Not
                      : Expression::Kind::NotationCall;
    if (result.kind == Expression::Kind::NotationCall) {
      auto projected77 = descriptor(id, symbol,
                                    kind(id) == K::Binary ? Position::Infix
                                                          : Position::Prefix);
      if (!projected77)
        return projected77.takeError();
      result.notation = std::move(*projected77);
    }
    for (auto part : operands) {
      if (auto error = append(part))
        return error;
    }
    break;
  }
  default:
    return fail(id, "this expression has no native layout execution projection",
                "source.layout-unavailable");
  }
  for (auto child : result.children)
    result.height = std::max(result.height, decl.expressions[child].height + 1);
  auto index = uint32_t(decl.expressions.size());
  decl.expressions.push_back(std::move(result));
  return index;
}
} // namespace zkc::language::detail
