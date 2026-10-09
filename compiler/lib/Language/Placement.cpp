#include "Placement.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
std::vector<unsigned> intersection(ArrayRef<unsigned> a, ArrayRef<unsigned> b) {
  std::vector<unsigned> out;
  std::set_intersection(a.begin(), a.end(), b.begin(), b.end(),
                        std::back_inserter(out));
  return out;
}
} // namespace
std::optional<Components> Placement::owner(Span span) {
  if (!types.charge(roster.size() + 1, span))
    return {};
  unsigned id = variables.size();
  variables.push_back({id, 0, roster, span, span});
  Components result(roster);
  result.owners.push_back(id);
  return result;
}
std::optional<Components> Placement::intersect(ArrayRef<Components> inputs,
                                               Span span) {
  Components result(roster);
  for (const auto &input : inputs) {
    if (!types.charge(result.roles.size() + input.roles.size() +
                          result.owners.size() + input.owners.size() + 1,
                      span))
      return {};
    result.roles = intersection(result.roles, input.roles);
    std::vector<unsigned> owners;
    std::set_union(result.owners.begin(), result.owners.end(),
                   input.owners.begin(), input.owners.end(),
                   std::back_inserter(owners));
    result.owners = std::move(owners);
  }
  return result;
}
bool Placement::form(const Components &value, Span span) {
  if (!types.charge(value.roles.size() + value.owners.size() + 1, span))
    return false;
  formation.emplace_back(value, span);
  return true;
}
unsigned Placement::root(unsigned id) {
  if (variables[id].parent != id)
    variables[id].parent = root(variables[id].parent);
  return variables[id].parent;
}
bool Placement::narrow(unsigned id, ArrayRef<unsigned> roles, Span span) {
  auto &v = variables[root(id)];
  if (!types.charge(v.domain.size() + roles.size() + 1, span))
    return false;
  auto domain = intersection(v.domain, roles);
  if (domain.empty())
    return types.fail(
        "source.roles",
        "participant constraints conflict at this operand or result", span,
        {v.reason, v.origin});
  if (domain != v.domain) {
    v.domain = std::move(domain);
    v.reason = span;
  }
  return true;
}
bool Placement::unite(unsigned a, unsigned b, Span span) {
  a = root(a);
  b = root(b);
  if (a == b)
    return true;
  if (variables[a].rank < variables[b].rank)
    std::swap(a, b);
  if (!narrow(a, variables[b].domain, span))
    return false;
  variables[b].parent = a;
  if (variables[a].rank == variables[b].rank)
    ++variables[a].rank;
  return true;
}
bool Placement::nonempty(const Components &value, Span span) {
  if (!types.charge(value.roles.size() + value.owners.size() + 1, span))
    return false;
  if (value.roles.empty())
    return types.fail("source.roles", "expression has no common participant",
                      span);
  if (value.owners.empty())
    return true;
  unsigned first = value.owners.front();
  for (auto variable : value.owners)
    if (!unite(first, variable, span))
      return false;
  return narrow(first, value.roles, span);
}
bool Placement::demand(const Components &value, ArrayRef<unsigned> roles,
                       Span span) {
  if (!nonempty(value, span))
    return false;
  if (!std::includes(value.roles.begin(), value.roles.end(), roles.begin(),
                     roles.end()))
    return types.fail("source.roles",
                      "expression is unavailable at the required participant",
                      span);
  if (roles.empty() || value.owners.empty())
    return true;
  if (roles.size() != 1)
    return types.fail("source.roles",
                      "one ordered call cannot supply several participants",
                      span);
  return narrow(value.owners.front(), roles, span);
}
bool Placement::together(const Components &a, const Components &b, Span span) {
  auto value = intersect({a, b}, span);
  return value && nonempty(*value, span);
}
std::vector<unsigned> Placement::resolve(const Components &value) {
  auto roles = value.roles;
  for (auto variable : value.owners)
    roles = intersection(roles, variables[root(variable)].domain);
  return roles;
}
unsigned Placement::selected(unsigned variable) {
  return variables[root(variable)].domain.front();
}
bool Placement::solve() {
  // Check uniqueness before formation: unused mathematics cannot choose where
  // an effect happens, even if only one of its possible placements forms.
  for (unsigned i = 0; i < variables.size(); ++i) {
    const auto &domain = variables[root(i)].domain;
    if (domain.size() != 1) {
      std::string candidates;
      for (auto role : domain) {
        if (!candidates.empty())
          candidates += ", ";
        candidates += decl.roles[role];
      }
      return types.fail(
          "source.owner",
          "ambiguous participant (" + candidates +
              "); constrain this statement with @Role or an owned operand",
          variables[i].origin, {variables[root(i)].reason});
    }
  }
  for (const auto &[value, span] : formation) {
    if (!types.charge(value.roles.size() + value.owners.size() + 1, span))
      return false;
    if (resolve(value).empty())
      return types.fail("source.roles",
                        "original mathematical expression has no common "
                        "participant at the selected owners",
                        span);
  }
  return true;
}
} // namespace zkc::language::detail
