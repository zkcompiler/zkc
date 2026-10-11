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
                                    Span span) {
  auto known = [&](Guard a, Guard b) -> std::optional<Guard> {
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
    auto found = combinations.find({disjunction, a, b});
    return found == combinations.end() ? std::nullopt
                                       : std::optional(found->second);
  };
  // An explicit work stack makes sequential guards independent of expression
  // nesting limits. Every expanded diagram edge consumes the shared work
  // budget.
  std::vector<std::pair<Guard, Guard>> pending{{a, b}};
  while (!pending.empty()) {
    auto [left, right] = pending.back();
    if (!types.charge(1, span))
      return never;
    if (known(left, right)) {
      pending.pop_back();
      continue;
    }
    auto variable = std::min(nodes[left].variable, nodes[right].variable);
    // Interning children can reallocate nodes; retain IDs by value.
    auto l = nodes[left], r = nodes[right];
    std::vector<Guard> children;
    bool complete = true;
    for (unsigned i = 0; i < arities[variable]; ++i) {
      if (!types.charge(1, span))
        return never;
      Guard x = l.variable == variable ? l.children[i] : left;
      Guard y = r.variable == variable ? r.children[i] : right;
      if (auto child = known(x, y))
        children.push_back(*child);
      else {
        pending.emplace_back(x, y);
        complete = false;
        break;
      }
    }
    if (!complete)
      continue;
    auto result = node(variable, std::move(children), span);
    if (types.diagnostic)
      return never;
    if (left > right)
      std::swap(left, right);
    combinations.emplace(std::make_tuple(disjunction, left, right), result);
    pending.pop_back();
  }
  return *known(a, b);
}
UsagePlan::Guard UsagePlan::intersect(Guard a, Guard b, Span span) {
  return combine(false, a, b, span);
}
UsagePlan::Guard UsagePlan::unite(Guard a, Guard b, Span span) {
  return combine(true, a, b, span);
}
UsagePlan::Value UsagePlan::own(const Type &type, Span span, Guard guard) {
  unsigned origin = origins.size();
  origins.push_back({type, span, {}});
  return {{{}, origin, {}, guard, {}}};
}
UsagePlan::Value UsagePlan::join(Value value, Span span) {
  for (auto &part : value) {
    if (!types.charge(part.sourcePath.size() + part.transfers.size() + 1, span))
      return {};
    auto found = llvm::find_if(part.transfers, [&](const auto &transfer) {
      return transfer.path == part.sourcePath;
    });
    if (found == part.transfers.end())
      part.transfers.push_back({part.sourcePath, order});
    else
      found->before = order;
  }
  return value;
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
      result.push_back(
          {{}, part.origin, std::move(source), part.guard, part.transfers});
    } else if (prefix(path, part.path)) {
      result.push_back({std::vector<unsigned>(part.path.begin() + path.size(),
                                              part.path.end()),
                        part.origin, part.sourcePath, part.guard,
                        part.transfers});
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
    origins[part.origin].uses.push_back({std::move(part.sourcePath), part.guard,
                                         span, order,
                                         std::move(part.transfers)});
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
  auto properties = types.permissions(type, exit.span, &scope);
  if (!properties)
    return false;
  if (properties->drop)
    return true;
  Guard covered = never;
  for (const auto &use : origins[exit.origin].uses) {
    if (!types.charge(use.path.size() + 1, exit.span))
      return false;
    if ((!exit.before || use.order <= *exit.before) && prefix(use.path, path))
      covered = unite(covered, use.guard, exit.span);
  }
  // Reduced diagrams are canonical: this implication needs no complement walk.
  if (intersect(exit.guard, covered, exit.span) == exit.guard)
    return !types.diagnostic;
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
  // A path's prefix unions replace pairwise comparisons of all its uses.
  // Once Copy is required for that path, later duplication adds no condition.
  struct History {
    Type type;
    bool copy;
    std::vector<std::pair<uint64_t, Guard>> prefixes;
  };
  for (const auto &origin : origins) {
    std::map<std::vector<unsigned>, History> paths;
    for (const auto &use : origin.uses) {
      for (auto &[path, history] : paths) {
        if (!types.charge(path.size() + use.path.size() + use.transfers.size() +
                              1,
                          use.span))
          return false;
        if (history.copy)
          continue;
        Guard prior = never;
        if (prefix(path, use.path) || prefix(use.path, path))
          prior = history.prefixes.back().second;
        for (const auto &transfer : use.transfers) {
          if (!types.charge(transfer.path.size() + 1, use.span))
            return false;
          if (!prefix(path, transfer.path) && !prefix(transfer.path, path))
            continue;
          auto at = std::upper_bound(history.prefixes.begin(),
                                     history.prefixes.end(), transfer.before,
                                     [](uint64_t order, const auto &entry) {
                                       return order < entry.first;
                                     });
          if (at != history.prefixes.begin())
            prior = unite(prior, std::prev(at)->second, use.span);
        }
        if (intersect(prior, use.guard, use.span) == never)
          continue;
        if (!require(history.type, Usage::Copy, use.span, "source.move",
                     "value or joined state was already moved"))
          return false;
        history.copy = true;
      }
      auto found = paths.find(use.path);
      if (found == paths.end()) {
        auto type = types.projectedType(scope, origin.type, use.path, use.span);
        auto properties =
            type ? types.permissions(*type, use.span, &scope) : std::nullopt;
        if (!properties)
          return false;
        found =
            paths.emplace(use.path, History{*type, properties->copy, {}}).first;
      }
      auto &history = found->second;
      if (!history.copy) {
        Guard previous =
            history.prefixes.empty() ? never : history.prefixes.back().second;
        history.prefixes.emplace_back(use.order,
                                      unite(previous, use.guard, use.span));
      }
    }
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
