#include "TypeInference.h"
#include "zkc/Language/Diagnostics.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
TypeInference::Variable TypeInference::fresh(Span span) {
  types.charge(1, span);
  auto id = nodes.size();
  nodes.push_back({unsigned(id), 0, span, {}, {}});
  return id;
}
TypeInference::Variable TypeInference::root(Variable id) {
  auto parent = id;
  while (nodes[parent].parent != parent)
    parent = nodes[parent].parent;
  while (nodes[id].parent != id) {
    auto next = nodes[id].parent;
    nodes[id].parent = parent;
    id = next;
  }
  return parent;
}
TypeInference::Variable
TypeInference::shape(Type head, std::vector<Variable> arguments, Span span) {
  auto id = fresh(span);
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
  return instantiate(type, parameters, span, 1);
}
TypeInference::Variable TypeInference::instantiate(const Type &type,
                                                   const Parameters &parameters,
                                                   Span span, unsigned depth) {
  if (types.diagnostic || depth > types.work.limits.typeDepth ||
      !types.charge(1, span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "inference type depth exceeded", span);
    return fresh(span);
  }
  if (type.symbolic && type.kind != Type::Kind::Associated &&
      (type.kind != Type::Kind::Natural ||
       (!type.domain.empty() &&
        type.dimension == cantFail(Natural::atom(type.domain)))))
    if (auto it = parameters.find(type.domain); it != parameters.end())
      return it->second;
  // Associated types are forward functions, not injective constructors.
  if (!parameters.empty() &&
      (type.kind == Type::Kind::Associated || !domainSort(type).empty()) &&
      !type.arguments.empty()) {
    auto base =
        instantiate(type.arguments.front(), parameters, span, depth + 1);
    auto result = fresh(span);
    auto name = StringRef(type.domain).rsplit("::").second.str();
    defer([this, base, result, name, span] {
      auto input = get(base, span);
      if (!input)
        return false;
      auto output = types.associated(*input, name, span);
      if (output)
        equal(result, known(*output, span), span);
      return true;
    });
    return result;
  }
  if (type.kind == Type::Kind::Natural) {
    Parameters dependencies;
    for (const auto &[factors, coefficient] : type.dimension.terms()) {
      (void)coefficient;
      for (const auto &factor : factors)
        if (auto it = parameters.find(factor.name); it != parameters.end())
          dependencies.insert(*it);
    }
    if (!dependencies.empty()) {
      auto result = fresh(span);
      defer([this, result, type, dependencies, span] {
        Substitution substitution;
        for (auto &[name, variable] : dependencies) {
          auto value = get(variable, span);
          if (!value)
            return false;
          substitution.emplace(name, *value);
        }
        auto output = types.substitute(type, substitution, span);
        if (output)
          equal(result, known(*output, span), span);
        return true;
      });
      return result;
    }
  }
  std::vector<Variable> arguments;
  for (const auto &argument : type.arguments)
    arguments.push_back(instantiate(argument, parameters, span, depth + 1));
  if (type.kind == Type::Kind::Array) {
    Type dimension(Type::Kind::Natural);
    dimension.dimension = type.dimension;
    // A normalized bare atom is the only invertible dimension pattern.
    const auto &terms = type.dimension.terms();
    if (terms.size() == 1 && terms.begin()->second == 1 &&
        terms.begin()->first.size() == 1 &&
        terms.begin()->first.front().kind == Natural::Factor::Kind::Atom) {
      dimension.domain = terms.begin()->first.front().name;
      dimension.symbolic = true;
    }
    arguments.push_back(instantiate(dimension, parameters, span, depth + 1));
  }
  return shape(type, std::move(arguments), span);
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
  const auto left = nodes[a], right = nodes[b];
  auto kinds = left.kinds & right.kinds;
  auto conflict = [&] {
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
      for (unsigned kind = 0; kind <= unsigned(Type::Kind::Asset); ++kind)
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
    if (*left.head != *right.head ||
        left.arguments.size() != right.arguments.size())
      return conflict();
    for (unsigned i = 0; i < left.arguments.size(); ++i)
      if (!equal(left.arguments[i], right.arguments[i], span, depth + 1))
        return false;
  } else if (occurs(a, b, span) || occurs(b, a, span)) {
    return types.diagnostic ? false
                            : types.fail("source.inference",
                                         "recursive inferred type", span);
  }
  if (nodes[a].rank < nodes[b].rank)
    std::swap(a, b);
  nodes[b].parent = a;
  if (nodes[a].rank == nodes[b].rank)
    ++nodes[a].rank;
  if (!nodes[a].head) {
    nodes[a].head = nodes[b].head;
    nodes[a].arguments = nodes[b].arguments;
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
  auto &node = nodes[root(id)];
  mask &= node.kinds;
  if (!mask)
    return types.fail("source.type",
                      "expression needs a compatible scalar type", span,
                      {node.origin});
  if (mask != node.kinds) {
    node.kinds = mask;
    ++revision;
  }
  return true;
}
bool TypeInference::allows(Variable id, Type::Kind kind) {
  return nodes[root(id)].kinds & (uint32_t(1) << unsigned(kind));
}
std::optional<Type> TypeInference::get(Variable id, Span span) {
  return get(id, span, 1);
}
std::optional<Type> TypeInference::get(Variable id, Span span, unsigned depth) {
  if (types.diagnostic || depth > types.work.limits.typeDepth ||
      !types.charge(1, span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "inference type depth exceeded", span);
    return {};
  }
  const auto &node = nodes[root(id)];
  if (!node.head)
    return {};
  Type result = *node.head;
  for (auto child : node.arguments) {
    auto type = get(child, span, depth + 1);
    if (!type)
      return {};
    result.arguments.push_back(std::move(*type));
  }
  if (result.kind == Type::Kind::Array) {
    result.dimension = result.arguments.back().dimension;
    result.arguments.pop_back();
  }
  if (!types.chargeType(result, span))
    return {};
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
} // namespace zkc::language::detail
