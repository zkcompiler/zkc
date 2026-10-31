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
UsagePlan::Guard UsagePlan::ancestorAtDepth(Guard guard, unsigned depth) const {
  unsigned distance = nodes[guard].depth - depth;
  for (unsigned bit = 0; distance; ++bit, distance >>= 1)
    if (distance & 1)
      guard = nodes[guard].ancestors[bit];
  return guard;
}
UsagePlan::Guard UsagePlan::commonAncestor(Guard a, Guard b) const {
  unsigned depth = std::min(nodes[a].depth, nodes[b].depth);
  a = ancestorAtDepth(a, depth);
  b = ancestorAtDepth(b, depth);
  if (a == b)
    return a;
  for (unsigned bit = nodes[a].ancestors.size(); bit-- > 0;)
    if (bit < nodes[a].ancestors.size() &&
        nodes[a].ancestors[bit] != nodes[b].ancestors[bit]) {
      a = nodes[a].ancestors[bit];
      b = nodes[b].ancestors[bit];
    }
  return nodes[a].ancestors.front();
}
bool UsagePlan::impliesAncestor(Guard guard, Guard ancestor) const {
  return nodes[guard].depth >= nodes[ancestor].depth &&
         ancestorAtDepth(guard, nodes[ancestor].depth) == ancestor;
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
  Guard ancestor = never;
  for (Guard child : children)
    if (child != never)
      ancestor = ancestor == never ? child : commonAncestor(ancestor, child);
  Node next{
      variable, std::move(children), nodes[ancestor].depth + 1, {ancestor}};
  for (unsigned bit = 0; bit < nodes[next.ancestors.back()].ancestors.size();
       ++bit)
    next.ancestors.push_back(nodes[next.ancestors.back()].ancestors[bit]);
  if (!types.charge(next.ancestors.size(), span))
    return never;
  Guard result = nodes.size();
  nodes.push_back(std::move(next));
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
    // Ancestors were allocated before their descendants. This implication is
    // only a shortcut; the ordinary decision-graph operation handles all other
    // relationships, including implications absent from the ancestor tree.
    if (impliesAncestor(b, a))
      return disjunction ? a : b;
    auto found = combinations.find({disjunction, a, b});
    return found == combinations.end() ? std::nullopt
                                       : std::optional(found->second);
  };
  // An explicit work stack makes sequential guards independent of expression
  // nesting limits. Every expanded diagram edge consumes the shared work
  // budget.
  struct Pending {
    Guard left, right;
    unsigned variable = 0;
    bool expanded = false;
    std::vector<Guard> children;
  };
  std::vector<Pending> pending{{a, b, 0, false, {}}};
  while (!pending.empty()) {
    if (!types.charge(1, span))
      return never;
    auto &frame = pending.back();
    if (known(frame.left, frame.right)) {
      pending.pop_back();
      continue;
    }
    if (!frame.expanded) {
      // New decisions precede older ones, so extending a continuing guard
      // shares its existing diagram instead of copying the whole prefix.
      frame.variable =
          std::max(nodes[frame.left].variable, nodes[frame.right].variable);
      if (!types.charge(arities[frame.variable], span))
        return never;
      frame.children.reserve(arities[frame.variable]);
      frame.expanded = true;
    }
    bool complete = true;
    while (frame.children.size() < arities[frame.variable]) {
      if (!types.charge(1, span))
        return never;
      auto i = frame.children.size();
      Guard x = nodes[frame.left].variable == frame.variable
                    ? nodes[frame.left].children[i]
                    : frame.left;
      Guard y = nodes[frame.right].variable == frame.variable
                    ? nodes[frame.right].children[i]
                    : frame.right;
      if (auto child = known(x, y))
        frame.children.push_back(*child);
      else {
        // Keep completed children while the nested pair is resolved. Node IDs
        // remain valid even if either vector reallocates during that work.
        pending.push_back({x, y, 0, false, {}});
        complete = false;
        break;
      }
    }
    if (!complete)
      continue;
    auto result = node(frame.variable, std::move(frame.children), span);
    if (types.diagnostic)
      return never;
    auto [left, right] = std::minmax(frame.left, frame.right);
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
UsagePlan::Value UsagePlan::join(Value value, const Type &type, Span span) {
  Value retained, transferable;
  for (auto &part : value) {
    if (!types.charge(part.sourcePath.size() + part.transfers.size() + 1, span))
      return {};
    bool untouched = true;
    for (const auto &use : origins[part.origin].uses) {
      if (!types.charge(use.path.size() + part.sourcePath.size() + 1, span))
        return {};
      if ((prefix(use.path, part.sourcePath) ||
           prefix(part.sourcePath, use.path)) &&
          intersect(use.guard, part.guard, span) != never) {
        untouched = false;
        break;
      }
    }
    if (untouched) {
      transferable.push_back(std::move(part));
      continue;
    }
    // A possibly consumed predecessor remains conditional: using its whole
    // successor later must still account for earlier partial moves.
    auto found = llvm::find_if(part.transfers, [&](const auto &transfer) {
      return transfer.path == part.sourcePath;
    });
    if (found == part.transfers.end())
      part.transfers.push_back({part.sourcePath, order});
    else
      found->before = order;
    retained.push_back(std::move(part));
  }
  if (!transferable.empty()) {
    // On these paths no predecessor has been used. Transfer it now, exactly
    // like final elaboration, and give equivalent output fields one fresh
    // origin. Repeated joins then retain state, not every historical alias.
    std::map<std::vector<unsigned>, Guard> fields;
    for (const auto &part : transferable) {
      if (!use({part}, {}, part.guard, span))
        return {};
      auto &guard = fields[part.path];
      guard = unite(guard, part.guard, span);
    }
    auto origin = own(type, span, always).front().origin;
    for (auto &[path, guard] : fields)
      retained.push_back({path, origin, path, guard, {}});
  }
  return retained;
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
                            std::optional<Coverage> &coverage,
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
  // Index an origin's uses once, only if it has a non-Drop obligation.
  // A field is covered by uses of itself or an ancestor, never its siblings.
  if (!coverage) {
    coverage.emplace();
    for (const auto &use : origins[exit.origin].uses) {
      if (!types.charge(use.path.size() + 1, exit.span))
        return false;
      auto &history = (*coverage)[use.path];
      Guard previous = history.empty() ? never : history.back().second;
      history.emplace_back(use.order, unite(previous, use.guard, exit.span));
    }
  }
  Guard covered = never;
  for (unsigned i = 0; i <= path.size(); ++i) {
    if (!types.charge(i + 1, exit.span))
      return false;
    auto found = coverage->find({path.begin(), path.begin() + i});
    if (found == coverage->end())
      continue;
    const auto &history = found->second;
    auto at =
        exit.before
            ? std::upper_bound(history.begin(), history.end(), *exit.before,
                               [](uint64_t order, const auto &entry) {
                                 return order < entry.first;
                               })
            : history.end();
    if (at != history.begin())
      covered = unite(covered, std::prev(at)->second, exit.span);
  }
  // Reduced diagrams are canonical: this implication needs no complement walk.
  if (intersect(exit.guard, covered, exit.span) == exit.guard)
    return !types.diagnostic;
  const auto *decl = types.typeDeclaration(type);
  bool structural =
      type.kind == Type::Kind::Tuple ||
      ((type.kind == Type::Kind::Record ||
        type.kind == Type::Kind::LogicalRecord) &&
       decl && !decl->sealed) ||
      (type.kind == Type::Kind::Array && type.dimension.isClosed());
  if (structural) {
    auto fields = types.fields(type, exit.span);
    if (!fields)
      return false;
    if (!fields->empty()) {
      for (unsigned i = 0; i < fields->size(); ++i) {
        auto child = path;
        child.push_back(i);
        if (!finishPlace(exit, (*fields)[i].type, std::move(child), coverage,
                         require, depth + 1))
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
    std::vector<std::pair<uint64_t, Guard>> prefixes;
  };
  for (const auto &origin : origins) {
    std::map<std::vector<unsigned>, History> paths;
    std::set<std::vector<unsigned>> reusable;
    for (const auto &use : origin.uses) {
      std::set<std::vector<unsigned>> overlaps;
      auto include = [&](ArrayRef<unsigned> path) {
        // Ordered paths make each subtree a contiguous range. Only ancestor
        // and descendant histories can overlap this use or whole-value join.
        for (unsigned i = 0; i < path.size(); ++i) {
          if (!types.charge(i + 1, use.span))
            return false;
          auto ancestor = paths.find({path.begin(), path.begin() + i});
          if (ancestor != paths.end())
            overlaps.insert(ancestor->first);
        }
        std::vector<unsigned> key(path.begin(), path.end());
        for (auto at = paths.lower_bound(key);
             at != paths.end() && prefix(path, at->first); ++at) {
          if (!types.charge(at->first.size() + 1, use.span))
            return false;
          overlaps.insert(at->first);
        }
        return true;
      };
      if (!include(use.path))
        return false;
      for (const auto &transfer : use.transfers)
        if (!include(transfer.path))
          return false;
      for (const auto &path : overlaps) {
        auto &history = paths.at(path);
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
        reusable.insert(path);
        paths.erase(path);
      }
      if (reusable.count(use.path))
        continue;
      auto found = paths.find(use.path);
      if (found == paths.end()) {
        auto type = types.projectedType(scope, origin.type, use.path, use.span);
        auto properties =
            type ? types.permissions(*type, use.span, &scope) : std::nullopt;
        if (!properties)
          return false;
        if (properties->copy) {
          reusable.insert(use.path);
          continue;
        }
        found = paths.emplace(use.path, History{*type, {}}).first;
      }
      auto &history = found->second;
      Guard previous =
          history.prefixes.empty() ? never : history.prefixes.back().second;
      history.prefixes.emplace_back(use.order,
                                    unite(previous, use.guard, use.span));
    }
  }
  std::map<unsigned, std::optional<Coverage>> coverage;
  for (const auto &exit : exits) {
    auto type = types.projectedType(scope, origins[exit.origin].type, exit.path,
                                    exit.span);
    if (!type ||
        !finishPlace(exit, *type, exit.path, coverage[exit.origin], require, 1))
      return false;
  }
  return !types.diagnostic;
}
} // namespace zkc::language::detail
