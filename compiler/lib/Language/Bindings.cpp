#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::pair<BindingId, std::vector<unsigned>>>
BodyChecker::sourcePlace(uint32_t id, unsigned depth) {
  const auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span)) {
    if (!checker.types.diagnostic)
      fail("source.limit", "place depth limit", expr.span);
    return {};
  }
  if (expr.kind == Expression::Kind::Name) {
    if (!expr.binding || !bindings.count(*expr.binding)) {
      fail("source.name", "expected an available data binding: " + expr.text,
           expr.span);
      return {};
    }
    return std::make_pair(*expr.binding, std::vector<unsigned>{});
  }
  if (expr.kind != Expression::Kind::Projection) {
    fail("source.place", "field access requires a named place", expr.span);
    return {};
  }
  auto base = sourcePlace(expr.children.front(), depth + 1);
  if (!base)
    return {};
  auto type = projected(bindings.at(base->first).type, base->second, expr.span);
  if (!type)
    return {};
  if (expr.bracket != (type->kind == Type::Kind::Array)) {
    fail("source.index", "use brackets for arrays and dots for product fields",
         expr.span);
    return {};
  }
  auto index = checker.types.fieldIndex(decl, *type, expr.text, expr.span);
  if (!index)
    return {};
  base->second.push_back(*index);
  if (!projected(bindings.at(base->first).type, base->second, expr.span))
    return {};
  return base;
}
std::optional<std::pair<ValueId, std::vector<unsigned>>>
BodyChecker::place(uint32_t id, unsigned depth) {
  auto p = sourcePlace(id, depth);
  if (!p)
    return {};
  return place(FreePlace{p->first, p->second}, syntax.expressions[id].span);
}
std::optional<std::pair<ValueId, std::vector<unsigned>>>
BodyChecker::place(const FreePlace &p, Span span) {
  const auto &state = bindings.at(p.binding);
  if (state.value)
    return std::make_pair(*state.value, p.path);
  for (auto &[path, value] : state.pieces) {
    if (!checker.types.charge(path.size() + 1, span))
      return {};
    if (path.size() <= p.path.size() &&
        std::equal(path.begin(), path.end(), p.path.begin()))
      return std::make_pair(
          value,
          std::vector<unsigned>(p.path.begin() + path.size(), p.path.end()));
  }
  fail("source.move", "binding is unavailable on this continuing path", span);
  return {};
}
std::optional<ValueId>
BodyChecker::project(ValueId value, ArrayRef<unsigned> path, Span span) {
  auto type = projected(body.values[value.index].type, path, span);
  if (!type || !use(value, span, path))
    return {};
  return emit(
      Projection{value, std::vector<unsigned>(path.begin(), path.end())}, *type,
      body.values[value.index].components, span);
}
std::optional<ValueId> BodyChecker::fresh(ValueId value, Span span) {
  return project(value, {}, span);
}
bool BodyChecker::discard(ValueId value, Span span) {
  auto caps =
      checker.types.permissions(body.values[value.index].type, span, &decl);
  return caps &&
         (caps->drop ||
          fail("source.drop", "discarding a value requires Drop", span)) &&
         use(value, span);
}
std::optional<ValueId>
BodyChecker::restrictRoles(ValueId value, ArrayRef<unsigned> roles, Span span) {
  if (!active(roles, span))
    return {};
  auto before = body.values[value.index];
  if (!std::includes(before.components.begin(), before.components.end(),
                     roles.begin(), roles.end())) {
    fail("source.roles", "binding cannot gain participant availability", span);
    return {};
  }
  if (ArrayRef<unsigned>(before.components) == roles)
    return value;
  auto caps = checker.types.permissions(before.type, span, &decl);
  if (!caps || !checker.types.executableType(before.type, span))
    return {};
  if (!caps->drop) {
    fail("source.permission",
         "restriction cannot discard a component without Drop", span);
    return {};
  }
  if (!use(value, span))
    return {};
  std::vector<unsigned> selected(roles.begin(), roles.end());
  return emit(Restriction{value, selected}, before.type, selected, span);
}
bool BodyChecker::assign(BindingId id, ValueId value, Span span) {
  auto &state = bindings.at(id);
  if (body.values[value.index].type != state.type)
    return fail("source.type", "assignment cannot change the binding type",
                span);
  if (protocol()) {
    auto narrowed = restrictRoles(value, state.roles, span);
    if (!narrowed)
      return false;
    value = *narrowed;
  }
  // The RHS has already been evaluated, including any use of the old value.
  auto next = fresh(value, span);
  if (!next || (state.value && !finishValue(*state.value, span)))
    return false;
  state.value = *next;
  state.pieces.clear();
  return true;
}
bool BodyChecker::bindPattern(const Pattern &p, ValueId value, unsigned depth) {
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, p.span))
    return checker.types.diagnostic
               ? false
               : fail("source.limit", "binding pattern depth", p.span);
  auto type = body.values[value.index].type;
  if (p.kind == Pattern::Kind::Name) {
    auto alias = fresh(value, p.span);
    if (!alias)
      return false;
    bindings.emplace(
        *p.binding,
        BindingState{type, body.values[alias->index].components, *alias, {}});
    return true;
  }
  if (p.kind == Pattern::Kind::Ignore)
    return discard(value, p.span);
  if (p.kind == Pattern::Kind::Unit)
    return type.kind == Type::Kind::Unit
               ? discard(value, p.span)
               : fail("source.binding", "unit pattern requires a unit value",
                      p.span);
  std::vector<TypeField> fields;
  if (p.kind == Pattern::Kind::Record) {
    auto specified = checker.type(decl, *p.type);
    if (!specified)
      return false;
    if (*specified != type || type.kind != Type::Kind::Record)
      return fail("source.type", "record pattern type differs", p.span);
    auto fs = checker.types.fields(type, p.span);
    if (!fs)
      return false;
    fields = *fs;
    if (restricted(type)) {
      if (!local())
        return fail("source.mode",
                    "opening a restricted wrapper requires local mode", p.span);
      if (!checker.types.constructorAllowed(decl, type))
        return fail("source.private",
                    "record pattern requires constructor authority", p.span);
      Type unpacked(fields.empty() ? Type::Kind::Unit : Type::Kind::Tuple);
      for (auto &field : fields)
        unpacked.arguments.push_back(field.type);
      if (!use(value, p.span))
        return false;
      auto parts = emit(Construct{{value}, {}, Construct::Kind::Unpack},
                        unpacked, {}, p.span);
      if (!parts)
        return false;
      value = *parts;
    }
  } else {
    if (type.kind != Type::Kind::Tuple)
      return fail("source.binding", "tuple pattern requires one tuple value",
                  p.span);
    for (unsigned i = 0; i < type.arguments.size(); ++i)
      fields.push_back({std::to_string(i), type.arguments[i], true, p.span});
  }
  if (fields.size() != p.children.size())
    return fail("source.binding", "pattern must cover every field exactly once",
                p.span);
  std::set<unsigned> seen;
  for (unsigned i = 0; i < p.children.size(); ++i) {
    unsigned index = i;
    if (p.kind == Pattern::Kind::Record) {
      auto field =
          llvm::find_if(fields, [&](auto &f) { return f.name == p.labels[i]; });
      if (field == fields.end())
        return fail("source.field", "unknown pattern field", p.span);
      index = field - fields.begin();
      if (!field->isPublic && !checker.types.constructorAllowed(decl, type))
        return fail("source.private", "pattern field is private", p.span);
    }
    if (!seen.insert(index).second)
      return fail("source.binding", "duplicate pattern field", p.span);
    auto field = project(value, {index}, p.children[i].span);
    if (!field || !bindPattern(p.children[i], *field, depth + 1))
      return false;
  }
  return !fields.empty() || discard(value, p.span);
}
bool BodyChecker::bindResults(const Statement &s, ArrayRef<ValueId> values) {
  if (s.kind == Statement::Kind::Expression) {
    for (auto value : values)
      if (!discard(value, s.span))
        return false;
    return true;
  }
  if (values.size() == 1) {
    auto value = values.front();
    if (s.type) {
      auto expected = checker.type(decl, *s.type);
      if (!expected ||
          (*expected != body.values[value.index].type &&
           !fail("source.type", "binding annotation differs from result",
                 s.span)))
        return false;
    }
    if (s.roles) {
      auto roles = checker.roles(decl, *s.roles, s.span);
      auto restricted =
          roles ? restrictRoles(value, *roles, s.span) : std::nullopt;
      if (!restricted)
        return false;
      value = *restricted;
    }
    return s.kind == Statement::Kind::Assign
               ? assign(*s.pattern.binding, value, s.span)
               : bindPattern(s.pattern, value);
  }
  if (s.kind != Statement::Kind::Let || s.type || s.roles || s.mutableBinding)
    return fail(
        "source.binding",
        "separate protocol results require an unannotated tuple pattern",
        s.span);
  if (values.empty())
    return s.pattern.kind == Pattern::Kind::Unit ||
           fail("source.binding", "zero results require () or a call statement",
                s.span);
  if (s.pattern.kind != Pattern::Kind::Tuple ||
      s.pattern.children.size() != values.size())
    return fail("source.binding",
                "bind one pattern per protocol result port; results are not a "
                "tuple value",
                s.span);
  for (unsigned i = 0; i < values.size(); ++i)
    if (!bindPattern(s.pattern.children[i], values[i]))
      return false;
  return true;
}
std::optional<ValueId> BodyChecker::pack(ArrayRef<ValueId> values, Span span) {
  if (values.size() == 1)
    return values.front();
  Type type(values.empty() ? Type::Kind::Unit : Type::Kind::Tuple);
  for (auto value : values) {
    type.arguments.push_back(body.values[value.index].type);
    if (!use(value, span))
      return {};
  }
  auto roles = combine(values, span);
  return roles ? emit(Construct{std::vector<ValueId>(values.begin(),
                                                     values.end()),
                                {}},
                      type, *roles, span)
               : std::nullopt;
}
} // namespace zkc::language::detail
