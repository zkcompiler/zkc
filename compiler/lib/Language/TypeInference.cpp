#include "TypeInference.h"
#include "zkc/Language/Diagnostics.h"
#include "llvm/ADT/STLExtras.h"
#include <cassert>
using namespace llvm;
namespace zkc::language::detail {
TypeInference::Variable TypeInference::fresh(Span span) {
  auto id = nodes.size();
  if (types.diagnostic || !types.charge(1, span))
    return id;
  nodes.push_back({unsigned(id), 0, span, {}, {}});
  return id;
}
TypeInference::Variable TypeInference::root(Variable id) {
  auto parent = id;
  while (nodes[parent].parent != parent)
    parent = nodes[parent].parent;
  return parent;
}
TypeInference::Variable
TypeInference::shape(Type head, std::vector<Variable> arguments, Span span) {
  auto id = fresh(span);
  if (types.diagnostic)
    return id;
  head.arguments.clear();
  // Array dimensions are terms too, so a bare natural parameter participates
  // in the same equations as a type parameter.
  if (head.kind == Type::Kind::Array)
    head.dimension = Natural{};
  nodes[id].head = std::move(head);
  nodes[id].arguments = std::move(arguments);
  nodes[id].kinds = uint32_t(1) << unsigned(nodes[id].head->kind);
  return id;
}
TypeInference::Variable TypeInference::known(const Type &type, Span span) {
  return instantiate(type, {}, span);
}
TypeInference::Variable TypeInference::instantiate(const Type &type,
                                                   const Parameters &parameters,
                                                   Span span) {
  if (!types.chargeType(type, span))
    return fresh(span);
  return instantiate(type, parameters, span, span, 1);
}
TypeInference::Variable TypeInference::instantiate(const Type &type,
                                                   const Parameters &parameters,
                                                   Span span, Span origin) {
  if (!types.chargeType(type, span))
    return fresh(span);
  return instantiate(type, parameters, span, origin, 1);
}
TypeInference::Variable TypeInference::instantiate(const Type &type,
                                                   const Parameters &parameters,
                                                   Span span, Span origin,
                                                   unsigned depth) {
  if (types.diagnostic || depth > types.work.limits.typeDepth ||
      !types.charge(1, span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "inference type depth exceeded", span);
    return fresh(span);
  }
  if (type.symbolic && type.kind != Type::Kind::Associated &&
      type.kind != Type::Kind::OracleProjection &&
      (type.kind != Type::Kind::Natural ||
       (!type.domain.empty() &&
        type.dimension == cantFail(Natural::atom(type.domain)))))
    if (auto it = parameters.find(type.domain); it != parameters.end())
      return it->second;
  // Associated types are forward functions, not injective constructors.
  if (!parameters.empty() &&
      (type.kind == Type::Kind::Associated ||
       type.kind == Type::Kind::OracleProjection ||
       !domainSort(type).empty()) &&
      !type.arguments.empty()) {
    auto base = instantiate(type.arguments.front(), parameters, span, origin,
                            depth + 1);
    auto result = fresh(span);
    if (types.diagnostic)
      return result;
    nodes[result].origin = origin;
    if (!types.chargeType(type, span))
      return result;
    // Preserve the resolved projection, including its required declaration.
    // Normalization selects its recorded edge once the base becomes known.
    defer([this, base, result, projection = type, span, origin]() mutable {
      auto input = get(base, span);
      if (!input)
        return false;
      projection.arguments.front() = *input;
      auto output = types.substitute(projection, {}, span);
      if (output)
        equal(result, instantiate(*output, {}, span, origin), span);
      return true;
    });
    return result;
  }
  if (type.kind == Type::Kind::Natural) {
    Parameters dependencies;
    for (const auto &[factors, coefficient] : type.dimension.terms()) {
      (void)coefficient;
      for (const auto &factor : factors)
        if (auto it = parameters.find(factor.name);
            it != parameters.end() && !dependencies.count(it->first)) {
          if (!types.charge(it->first.size() + 1, span))
            return nodes.size();
          dependencies.insert(*it);
        }
    }
    if (!dependencies.empty()) {
      auto result = fresh(span);
      if (types.diagnostic)
        return result;
      nodes[result].origin = origin;
      for (const auto &[name, variable] : dependencies) {
        (void)variable;
        if (!types.charge(name.size() + 1, span))
          return result;
      }
      defer([this, result, type, dependencies, span, origin] {
        Substitution substitution;
        for (auto &[name, variable] : dependencies) {
          auto value = get(variable, span);
          if (!value)
            return false;
          substitution.emplace(name, *value);
        }
        auto output = types.substitute(type, substitution, span);
        if (output)
          equal(result, instantiate(*output, {}, span, origin), span);
        return true;
      });
      return result;
    }
  }
  std::vector<Variable> arguments;
  for (const auto &argument : type.arguments)
    arguments.push_back(
        instantiate(argument, parameters, span, origin, depth + 1));
  if (type.kind == Type::Kind::Array) {
    const auto &terms = type.dimension.terms();
    const std::string *atom = nullptr;
    bool dependent = false;
    for (const auto &[factors, coefficient] : terms) {
      (void)coefficient;
      for (const auto &factor : factors)
        dependent |= parameters.count(factor.name) != 0;
    }
    if (terms.size() == 1 && terms.begin()->second == 1 &&
        terms.begin()->first.size() == 1 &&
        terms.begin()->first.front().kind == Natural::Factor::Kind::Atom)
      atom = &terms.begin()->first.front().name;
    if (atom && parameters.count(*atom)) {
      if (!types.charge(1, span))
        return nodes.size();
      arguments.push_back(parameters.at(*atom));
    } else {
      // The outer stored-Type preflight pays one dimension copy. Move that
      // polynomial into its equation head; an Array head retains no dimension.
      // Only a dependent polynomial needs a deferred computation's extra copy.
      if (dependent) {
        uint64_t dimensionWork = 1;
        for (const auto &[factors, coefficient] : terms) {
          (void)coefficient;
          ++dimensionWork;
          for (const auto &factor : factors)
            dimensionWork += 1 + factor.name.size() + factor.member.size();
        }
        if (!types.charge(dimensionWork, span))
          return nodes.size();
      }
      Type dimension(Type::Kind::Natural);
      dimension.dimension = type.dimension;
      dimension.symbolic = !dimension.dimension.isClosed();
      if (dependent)
        arguments.push_back(
            instantiate(dimension, parameters, span, origin, depth));
      else {
        if (!types.charge(1, span))
          return nodes.size();
        auto variable = shape(std::move(dimension), {}, span);
        if (types.diagnostic)
          return variable;
        nodes[variable].origin = origin;
        arguments.push_back(variable);
      }
    }
  }
  if (types.diagnostic)
    return nodes.size();
  auto result = shape(typeHead(type, type.kind != Type::Kind::Array),
                      std::move(arguments), span);
  if (types.diagnostic)
    return result;
  nodes[result].origin = origin;
  return result;
}
bool TypeInference::occurs(Variable needle, Variable id, Span span,
                           unsigned depth) {
  if (types.diagnostic || depth > types.work.limits.typeDepth ||
      !types.charge(1, span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "inference type depth exceeded", span);
    return true;
  }
  id = root(id);
  if (id == needle)
    return true;
  for (auto child : nodes[id].arguments)
    if (occurs(needle, child, span, depth + 1))
      return true;
  return false;
}
bool TypeInference::equal(Variable a, Variable b, Span span) {
  return equal(a, b, span, 1);
}
bool TypeInference::equal(Variable a, Variable b, Span span, unsigned depth) {
  if (types.diagnostic || depth > types.work.limits.typeDepth ||
      !types.charge(1, span))
    return types.diagnostic ? false
                            : types.fail("source.limit",
                                         "inference type depth exceeded", span);
  a = root(a);
  b = root(b);
  if (a == b)
    return true;
  // equal() never grows nodes. Heads are inspected only before recursion;
  // retain just the child IDs needed across recursive unions, not owned head
  // Types that are copied and immediately discarded.
  const auto &left = nodes[a], &right = nodes[b];
  auto kinds = left.kinds & right.kinds;
  auto conflict = [&] {
    // Diagnostic spelling allocates its own metadata text.
    for (auto id : {a, b})
      if (nodes[id].head &&
          !types.chargeType(*nodes[id].head, span, /*complete=*/false))
        return false;
    auto describe = [](const Node &node) {
      if (node.head) {
        if (node.head->kind == Type::Kind::Tuple)
          return std::string("tuple with ") +
                 std::to_string(node.arguments.size()) + " elements";
        if (node.head->kind == Type::Kind::Array)
          return std::string("array");
        return formatType(*node.head);
      }
      std::string choices;
      for (unsigned kind = 0; kind <= unsigned(Type::Kind::DescriptorSequence);
           ++kind)
        if (node.kinds & (uint32_t(1) << kind)) {
          if (!choices.empty())
            choices += " or ";
          choices += typeKindName(Type::Kind(kind));
        }
      return choices;
    };
    return types.fail("source.type",
                      "type conflict: " + describe(left) + " versus " +
                          describe(right),
                      span, {left.origin, right.origin});
  };
  if (!kinds)
    return conflict();
  if (left.head && right.head) {
    // Bound both operands, then pay the single head comparison. Neither head
    // is copied; equality reads at most the larger operand's metadata.
    uint64_t comparison = 0;
    for (auto id : {a, b}) {
      auto cost =
          typeComplexity(*nodes[id].head, types.work.limits.typeNodes,
                         types.work.limits.typeDepth, types.work.remaining(),
                         nullptr, false, TypeWork::Copy);
      if (!cost)
        return types.accept(cost.takeError(), span);
      comparison = std::max(comparison, *cost);
    }
    if (!types.charge(comparison, span))
      return false;
    if (*left.head != *right.head ||
        left.arguments.size() != right.arguments.size())
      return conflict();
    if (!types.charge(left.arguments.size() + right.arguments.size() + 2, span))
      return false;
    const auto leftArguments = left.arguments, rightArguments = right.arguments;
    for (unsigned i = 0; i < leftArguments.size(); ++i)
      if (!equal(leftArguments[i], rightArguments[i], span, depth + 1))
        return false;
  } else if (occurs(a, b, span) || occurs(b, a, span)) {
    return types.diagnostic ? false
                            : types.fail("source.inference",
                                         "recursive inferred type", span);
  }
  if (nodes[a].rank < nodes[b].rank)
    std::swap(a, b);
  if (!save(a, span) || !save(b, span))
    return false;
  reconstructed.clear();
  nodes[b].parent = a;
  if (nodes[a].rank == nodes[b].rank)
    ++nodes[a].rank;
  if (!nodes[a].head) {
    nodes[a].head = std::move(nodes[b].head);
    nodes[a].arguments = std::move(nodes[b].arguments);
    nodes[a].origin = nodes[b].origin;
  }
  nodes[a].kinds = kinds;
  ++revision;
  return true;
}
bool TypeInference::requireKinds(Variable id,
                                 std::initializer_list<Type::Kind> kinds,
                                 Span span) {
  if (types.diagnostic || !types.charge(1, span))
    return false;
  uint32_t mask = 0;
  for (auto kind : kinds)
    mask |= uint32_t(1) << unsigned(kind);
  id = root(id);
  auto &node = nodes[id];
  mask &= node.kinds;
  if (!mask)
    return types.fail("source.type",
                      "expression needs a compatible scalar type", span,
                      {node.origin});
  if (mask != node.kinds) {
    if (!save(id, span))
      return false;
    reconstructed.clear();
    node.kinds = mask;
    ++revision;
  }
  return true;
}
bool TypeInference::allows(Variable id, Type::Kind kind) {
  if (types.diagnostic)
    return false;
  return nodes[root(id)].kinds & (uint32_t(1) << unsigned(kind));
}
std::optional<Type> TypeInference::get(Variable id, Span span) {
  if (types.diagnostic)
    return {};
  auto canonical = root(id);
  if (auto found = reconstructed.find(canonical);
      found != reconstructed.end()) {
    if (!types.chargeType(found->second, span, /*complete=*/false))
      return {};
    return found->second;
  }
  // Equations can share a solved child many times. Bound the expanded result,
  // not just each stored head, before the first reconstructed Type allocation.
  uint64_t remaining = types.work.limits.typeNodes;
  std::function<bool(Variable, unsigned, bool)> preflight =
      [&](Variable variable, unsigned depth, bool stored) {
        if ((stored && !remaining) || depth > types.work.limits.typeDepth)
          return types.fail("source.limit", "expanded inference type limit",
                            span);
        if (stored)
          --remaining;
        const auto &node = nodes[root(variable)];
        if (!node.head ||
            !types.chargeType(*node.head, span, /*complete=*/false) ||
            !types.charge(node.arguments.size() + 1, span))
          return false;
        if ((!stored && (node.head->kind != Type::Kind::Natural ||
                         !node.arguments.empty())) ||
            (node.head->kind == Type::Kind::Array &&
             node.arguments.size() != 2))
          return types.fail("source.type", "invalid inference Array dimension",
                            span);
        for (unsigned i = 0; i < node.arguments.size(); ++i) {
          // The last Array equation contributes a Natural dimension, not
          // another stored Type node or level. Its traversal and metadata still
          // cost work.
          bool dimension = node.head->kind == Type::Kind::Array &&
                           i + 1 == node.arguments.size();
          if (!preflight(node.arguments[i], dimension ? depth : depth + 1,
                         !dimension))
            return false;
        }
        return true;
      };
  if (!preflight(id, 1, true))
    return {};
  auto result = get(id, span, 1);
  if (result) {
    // One complete preflight immediately precedes and pays for the retained
    // copy. A second copy preflight here would traverse the identical result
    // again without another Type copy to account for.
    if (!types.chargeType(*result, span))
      return {};
    reconstructed.emplace(canonical, *result);
  }
  return result;
}

std::optional<TypeInference::Structure> TypeInference::structure(Variable id,
                                                                 Span span) {
  if (types.diagnostic)
    return {};
  const auto &node = nodes[root(id)];
  if (!types.charge(node.arguments.size() + 1, span) || !node.head ||
      !types.chargeType(*node.head, span, /*complete=*/false))
    return {};
  return Structure{*node.head, node.arguments};
}
std::optional<Type> TypeInference::get(Variable id, Span span, unsigned depth) {
  if (types.diagnostic || depth > types.work.limits.typeDepth ||
      !types.charge(1, span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "inference type depth exceeded", span);
    return {};
  }
  const auto &node = nodes[root(id)];
  // The public preflight already traversed and debited every occurrence's
  // head copy before any reconstruction allocation.
  if (!node.head)
    return {};
  Type result = *node.head;
  for (unsigned i = 0; i < node.arguments.size(); ++i) {
    bool dimension =
        result.kind == Type::Kind::Array && i + 1 == node.arguments.size();
    auto type = get(node.arguments[i], span, dimension ? depth : depth + 1);
    if (!type)
      return {};
    result.arguments.push_back(std::move(*type));
  }
  if (result.kind == Type::Kind::Array) {
    result.dimension = std::move(result.arguments.back().dimension);
    result.arguments.pop_back();
  }
  return result;
}
void TypeInference::defer(std::function<bool()> computation) {
  if (!types.diagnostic && !computation())
    pending.push_back(std::move(computation));
}
bool TypeInference::solve(Span span) {
  uint64_t before;
  do {
    before = revision;
    for (auto it = pending.begin(); it != pending.end();) {
      if (types.diagnostic || !types.charge(1, span))
        return false;
      if ((*it)())
        it = pending.erase(it);
      else
        ++it;
    }
  } while (before != revision);
  return !types.diagnostic;
}
bool TypeInference::save(Variable id, Span span) {
  if (!recording)
    return true;
  const auto &node = nodes[id];
  if (!types.charge(node.arguments.size() + 1, span) ||
      (node.head && !types.chargeType(*node.head, span, /*complete=*/false)))
    return false;
  trail.emplace_back(id, node);
  return true;
}
std::optional<TypeInference::Checkpoint> TypeInference::checkpoint(Span span) {
  if (!types.charge(pending.size() + 1, span))
    return {};
  recording = true;
  Checkpoint result;
  result.nodeCount = nodes.size();
  result.trailSize = trail.size();
  result.pending = pending;
  result.revision = revision;
  result.owner = this;
  return result;
}
bool TypeInference::restore(const Checkpoint &state, Span span) {
  if (state.owner != this || state.trailSize > trail.size() ||
      state.nodeCount > nodes.size())
    return types.fail("source.internal",
                      "invalid inference rollback checkpoint", span);
  if (!types.charge(trail.size() - state.trailSize + state.pending.size() + 1,
                    span))
    return false;
  reconstructed.clear();
  while (trail.size() > state.trailSize) {
    auto &saved = trail.back();
    nodes[saved.first] = std::move(saved.second);
    trail.pop_back();
  }
  nodes.resize(state.nodeCount);
  pending = state.pending;
  revision = state.revision;
  return true;
}
} // namespace zkc::language::detail
