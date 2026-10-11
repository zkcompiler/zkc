#include "UsagePlan.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language::detail {
namespace {
bool prefix(ArrayRef<unsigned> a, ArrayRef<unsigned> b) {
  return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.begin());
}
} // namespace

UsagePlan::UsagePlan(Semantics &types, const Declaration &scope)
    : types(types), scope(scope) {
  nodes.resize(2);
}
unsigned UsagePlan::branch(unsigned arms) {
  unsigned result = arities.size();
  arities.push_back(arms);
  return result;
}
UsagePlan::Guard UsagePlan::node(unsigned variable, std::vector<Guard> children,
                                 Span span) {
  if (!types.charge(children.size() + 1, span))
    return never;
  if (llvm::all_of(children,
                   [&](Guard child) { return child == children.front(); }))
    return children.front();
  auto key = std::make_pair(variable, children);
  auto found = unique.find(key);
  if (found != unique.end())
    return found->second;
  Guard result = nodes.size();
  nodes.push_back({variable, std::move(children)});
  unique.emplace(std::move(key), result);
  return result;
}
UsagePlan::Guard UsagePlan::arm(unsigned variable, unsigned ordinal,
                                Span span) {
  std::vector<Guard> children(arities[variable], never);
  children[ordinal] = always;
  return node(variable, std::move(children), span);
}
UsagePlan::Guard UsagePlan::combine(bool disjunction, Guard a, Guard b,
                                    Span span, unsigned depth) {
  if (!types.charge(1, span))
    return never;
  if (depth > types.work.limits.expressionDepth) {
    types.fail("source.limit", "usage branch depth exceeded", span);
    return never;
  }
  if (a > b)
    std::swap(a, b);
  if (a == b || b == (disjunction ? never : always))
    return a;
  if (a == (disjunction ? never : always))
    return b;
  if (a == (disjunction ? always : never))
    return a;
  if (b == (disjunction ? always : never))
    return b;
  auto key = std::make_tuple(disjunction, a, b);
  auto found = combinations.find(key);
  if (found != combinations.end())
    return found->second;
  auto variable = std::min(nodes[a].variable, nodes[b].variable);
  // Recursive interning may reallocate nodes, so retain child IDs by value.
  const auto left = nodes[a], right = nodes[b];
  std::vector<Guard> children;
  for (unsigned i = 0; i < arities[variable]; ++i) {
    children.push_back(combine(
        disjunction, left.variable == variable ? left.children[i] : a,
        right.variable == variable ? right.children[i] : b, span, depth + 1));
    if (types.diagnostic)
      return never;
  }
  auto result = node(variable, std::move(children), span);
  combinations.emplace(key, result);
  return result;
}
UsagePlan::Guard UsagePlan::intersect(Guard a, Guard b, Span span) {
  return combine(false, a, b, span);
}
UsagePlan::Guard UsagePlan::unite(Guard a, Guard b, Span span) {
  return combine(true, a, b, span);
}
UsagePlan::Guard UsagePlan::negate(Guard guard, Span span, unsigned depth) {
  if (guard < 2)
    return 1 - guard;
  if (depth > types.work.limits.expressionDepth || !types.charge(1, span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "usage branch depth exceeded", span);
    return never;
  }
  auto entry = nodes[guard];
  for (auto &child : entry.children)
    child = negate(child, span, depth + 1);
  return node(entry.variable, std::move(entry.children), span);
}
UsagePlan::Value UsagePlan::own(const Type &type, Span span, Guard guard) {
  unsigned origin = origins.size();
  origins.push_back({type, span, {}});
  return {{{}, origin, {}, guard}};
}
UsagePlan::Value UsagePlan::within(const Value &value, Guard guard, Span span) {
  Value result;
  for (auto part : value) {
    part.guard = intersect(part.guard, guard, span);
    if (part.guard != never)
      result.push_back(std::move(part));
  }
  return result;
}
UsagePlan::Value UsagePlan::project(const Value &value, ArrayRef<unsigned> path,
                                    Span span) {
  Value result;
  for (const auto &part : value) {
    if (!types.charge(part.path.size() + path.size() + 1, span))
      return {};
    if (prefix(part.path, path)) {
      auto source = part.sourcePath;
      source.insert(source.end(), path.begin() + part.path.size(), path.end());
      result.push_back({{}, part.origin, std::move(source), part.guard});
    } else if (prefix(path, part.path)) {
      result.push_back({std::vector<unsigned>(part.path.begin() + path.size(),
                                              part.path.end()),
                        part.origin, part.sourcePath, part.guard});
    }
  }
  return result;
}
UsagePlan::Value UsagePlan::product(ArrayRef<Value> fields, Span span) {
  Value result;
  for (unsigned i = 0; i < fields.size(); ++i)
    for (auto part : fields[i]) {
      if (!types.charge(part.path.size() + 1, span))
        return {};
      part.path.insert(part.path.begin(), i);
      result.push_back(std::move(part));
    }
  return result;
}
bool UsagePlan::use(const Value &value, ArrayRef<unsigned> path, Guard guard,
                    Span span) {
  auto selected = within(project(value, path, span), guard, span);
  ++order;
  for (auto &part : selected)
    origins[part.origin].uses.push_back(
        {std::move(part.sourcePath), part.guard, span, order});
  return !types.diagnostic;
}
bool UsagePlan::finish(const Value &value, Guard guard, Span span,
                       bool prefixOnly) {
  for (auto &part : within(value, guard, span))
    exits.push_back({part.origin, std::move(part.sourcePath), part.guard, span,
                     prefixOnly ? std::optional(order) : std::nullopt});
  return !types.diagnostic;
}
bool UsagePlan::finishPlace(const Exit &exit, const Type &type,
                            std::vector<unsigned> path,
                            const Requirement &require, unsigned depth) {
  if (depth > types.work.limits.typeDepth || !types.charge(1, exit.span))
    return types.diagnostic
               ? false
               : types.fail("source.limit", "usage obligation depth exceeded",
                            exit.span);
  Guard covered = never;
  for (const auto &use : origins[exit.origin].uses) {
    if (!types.charge(use.path.size() + 1, exit.span))
      return false;
    if ((!exit.before || use.order <= *exit.before) && prefix(use.path, path))
      covered = unite(covered, use.guard, exit.span);
  }
  if (intersect(exit.guard, negate(covered, exit.span), exit.span) == never)
    return !types.diagnostic;
  auto properties = types.permissions(type, exit.span, &scope);
  if (!properties)
    return false;
  if (properties->drop)
    return true;
  const auto *decl = types.typeDeclaration(type);
  bool structural =
      type.kind == Type::Kind::Tuple ||
      (type.kind == Type::Kind::Record && decl && !decl->sealed) ||
      (type.kind == Type::Kind::Array && type.dimension.isClosed());
  if (structural) {
    auto fields = types.fields(type, exit.span);
    if (!fields)
      return false;
    if (!fields->empty()) {
      for (unsigned i = 0; i < fields->size(); ++i) {
        auto child = path;
        child.push_back(i);
        if (!finishPlace(exit, (*fields)[i].type, std::move(child), require,
                         depth + 1))
          return false;
      }
      return true;
    }
  }
  return require(type, Usage::Drop, exit.span, "source.drop",
                 "value without Drop remains unused on a continuing path");
}
bool UsagePlan::solve(const Requirement &require) {
  // Every authored use is checked, including prefixes of stopped paths.
  for (const auto &origin : origins)
    for (unsigned i = 0; i < origin.uses.size(); ++i)
      for (unsigned j = 0; j < i; ++j) {
        const auto &use = origin.uses[i], &prior = origin.uses[j];
        if (!types.charge(use.path.size() + prior.path.size() + 1, use.span))
          return false;
        if ((!prefix(use.path, prior.path) && !prefix(prior.path, use.path)) ||
            intersect(use.guard, prior.guard, use.span) == never)
          continue;
        auto type =
            types.projectedType(scope, origin.type, prior.path, use.span);
        if (!type || !require(*type, Usage::Copy, use.span, "source.move",
                              "value or overlapping field was already moved"))
          return false;
      }
  for (const auto &exit : exits) {
    auto type = types.projectedType(scope, origins[exit.origin].type, exit.path,
                                    exit.span);
    if (!type || !finishPlace(exit, *type, exit.path, require, 1))
      return false;
  }
  return !types.diagnostic;
}
} // namespace zkc::language::detail
