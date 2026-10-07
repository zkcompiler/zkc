#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::control(const Expression &expr,
                                            std::optional<Type> expected,
                                            unsigned depth) {
  if (!local()) {
    fail("source.mode", "control flow requires an ordered local function",
         expr.span);
    return {};
  }
  const bool loop = expr.kind == Expression::Kind::For,
             match = expr.kind == Expression::Kind::Match;
  LocalControl operation;
  operation.kind = loop    ? LocalControl::Kind::For
                   : match ? LocalControl::Kind::Match
                           : LocalControl::Kind::If;
  std::vector<std::pair<std::string, ValueId>> captures, carry;
  std::vector<Alternative> alternatives;
  if (loop) {
    for (unsigned i = 0; i < 2; ++i) {
      auto value =
          expression(expr.children[i], Type(Type::Kind::Index), depth + 1);
      if (!value || !use(*value, expr.span))
        return {};
      operation.operands.push_back(*value);
    }
    for (unsigned i = 0; i < expr.labels.size(); ++i) {
      auto value = expression(expr.children[i + 2], {}, depth + 1);
      if (!value || !use(*value, expr.span))
        return {};
      carry.emplace_back(expr.labels[i], *value);
      operation.operands.push_back(*value);
    }
    operation.carried = carry.size();
    Type result(carry.empty() ? Type::Kind::Unit
                : carry.size() == 1
                    ? body.values[carry.front().second.index].type.kind
                    : Type::Kind::Tuple);
    if (carry.size() == 1)
      result = body.values[carry.front().second.index].type;
    else
      for (auto &[name, value] : carry)
        result.arguments.push_back(body.values[value.index].type);
    if (expected && *expected != result) {
      fail("source.type", "loop result must match its initial carry",
           expr.span);
      return {};
    }
    expected = result;
  } else {
    auto value = expression(
        expr.children.front(),
        match ? std::optional<Type>{} : std::optional<Type>(Type{}), depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    operation.operands.push_back(*value);
    if (match) {
      auto type = body.values[value->index].type;
      if (restricted(type) && !checker.constructorAllowed(decl, type)) {
        fail("source.private",
             "matching a restricted variant needs constructor authority",
             expr.span);
        return {};
      }
      auto alts = checker.alternatives(type, expr.span);
      if (!alts)
        return {};
      alternatives = std::move(*alts);
      if (alternatives.size() != expr.regions.size()) {
        fail("source.match", "match must cover every alternative exactly once",
             expr.span);
        return {};
      }
    }
  }
  for (auto &name : expr.captures) {
    auto it = bindings.find(name);
    if (it == bindings.end()) {
      fail("source.name", "unknown capture: " + name, expr.span);
      return {};
    }
    auto caps = checker.permissions(body.values[it->second.index].type,
                                    expr.span, &decl);
    if (!caps)
      return {};
    if (loop && !caps->copy) {
      fail("source.permission",
           "loop captures require Copy; move resources through carry",
           expr.span);
      return {};
    }
    if (!use(it->second, expr.span))
      return {};
    captures.emplace_back(name, it->second);
    operation.operands.push_back(it->second);
  }
  std::set<std::string> seen;
  for (unsigned ordinal = 0; ordinal < expr.regions.size(); ++ordinal) {
    unsigned index = ordinal;
    if (match) {
      const auto &alt = alternatives[ordinal];
      operation.alternatives.push_back(alt.name);
      auto found = llvm::find(expr.labels, alt.name);
      if (found == expr.labels.end()) {
        fail("source.match", "missing alternative: " + alt.name, expr.span);
        return {};
      }
      index = found - expr.labels.begin();
      if (!seen.insert(expr.labels[index]).second ||
          alt.fields.size() != expr.payloads[index].size()) {
        fail("source.match", "alternative payload count differs", expr.span);
        return {};
      }
    }
    auto region = std::make_shared<Body>();
    region->mode = Body::Mode::Local;
    BodyChecker nested(checker, decl, syntax, *region, callDepth);
    if (loop) {
      if (!nested.addInput(expr.text, Type(Type::Kind::Index), {}, expr.span))
        return {};
      for (auto &[name, value] : carry)
        if (!nested.addInput(name, body.values[value.index].type, {},
                             expr.span))
          return {};
    }
    if (match)
      for (unsigned j = 0; j < alternatives[ordinal].fields.size(); ++j)
        if (!nested.addInput(expr.payloads[index][j],
                             alternatives[ordinal].fields[j].type, {},
                             expr.span))
          return {};
    std::vector<ValueId> captureIds;
    for (auto &[name, value] : captures) {
      captureIds.push_back(ValueId{uint32_t(region->values.size())});
      if (!nested.addInput(name, body.values[value.index].type, {}, expr.span))
        return {};
      // A for backedge retains the exact capture even when the body does not
      // inspect it. This is an ordinary continuing-path use for no-Drop values.
      if (loop && !nested.use(captureIds.back(), expr.span))
        return {};
    }
    std::vector<Port> outputs;
    if (expected)
      outputs.push_back({"result", *expected, {}, expr.span});
    if (!nested.run(syntax.bodies[expr.regions[index]], outputs, false))
      return {};
    if (!region->stopped) {
      const auto &type = region->values[region->results.front().index].type;
      if (expected && *expected != type) {
        fail("source.type", "continuing control arms must yield the same type",
             expr.span);
        return {};
      }
      expected = type;
      if (loop)
        region->results.insert(region->results.end(), captureIds.begin(),
                               captureIds.end());
    }
    body.mayStop |= region->mayStop;
    body.opaque |= region->opaque;
    operation.regions.push_back(std::move(region));
  }
  if (!expected) {
    fail("source.inference",
         "control expression with no continuing arm needs an expected type",
         expr.span);
    return {};
  }
  return emit(std::move(operation), *expected, {}, expr.span);
}
} // namespace zkc::language::detail
