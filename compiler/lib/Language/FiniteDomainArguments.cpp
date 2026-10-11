#include "BodyCheck.h"
#include "FiniteDomains.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<DomainOperands> domainOperands(Semantics &types, const Body &body,
                                             ArrayRef<unsigned> roots,
                                             Span span) {
  DomainOperands result;
  std::vector<unsigned> pending(roots.begin(), roots.end());
  std::set<unsigned> seen;
  while (!pending.empty()) {
    auto index = pending.back();
    pending.pop_back();
    if (!types.charge(1, span))
      return {};
    if (!seen.insert(index).second)
      continue;
    if (index >= body.domainBindings.size()) {
      types.fail("source.finite-domain", "domain operand edge outside body",
                 span);
      return {};
    }
    const auto &domain = body.domainBindings[index];
    if (!types.charge(domain.operands.size() + domain.children.size(), span))
      return {};
    result.parameterized |= domain.kind == DomainBinding::Kind::Parameter;
    result.values.insert(result.values.end(), domain.operands.begin(),
                         domain.operands.end());
    pending.insert(pending.end(), domain.children.begin(),
                   domain.children.end());
  }
  return result;
}
bool BodyChecker::addDomain(BindingId id, const DomainParameter &parameter,
                            unsigned formal) {
  if (!checker.types.chargeType(parameter.item, parameter.span))
    return false;
  domains.emplace(id, body.domainBindings.size());
  body.domainBindings.push_back({DomainBinding::Kind::Parameter,
                                 parameter.item,
                                 {},
                                 {},
                                 0,
                                 formal,
                                 parameter.span});
  return true;
}
bool BodyChecker::inheritDomains(BodyChecker &nested,
                                 const std::set<BindingId> &selected,
                                 std::vector<unsigned> &arguments) {
  for (auto binding : selected) {
    auto index = domains.at(binding);
    const auto &domain = body.domainBindings[index];
    DomainParameter formal{syntax.bindings[binding.index].name, domain.item,
                           domain.span};
    if (!nested.addDomain(binding, formal, arguments.size()))
      return false;
    arguments.push_back(index);
  }
  return true;
}
bool BodyChecker::captureDomains(
    BodyChecker &nested, const std::set<BindingId> &selected,
    const std::function<std::optional<ValueId>(ValueId)> &capture, Span span) {
  std::vector<unsigned> pending;
  for (auto binding : selected)
    pending.push_back(domains.at(binding));
  std::set<unsigned> reachable;
  while (!pending.empty()) {
    auto index = pending.back();
    pending.pop_back();
    if (!checker.types.charge(1, span))
      return false;
    if (!reachable.insert(index).second)
      continue;
    if (index >= body.domainBindings.size())
      return fail("source.finite-domain", "captured domain edge outside body",
                  span);
    const auto &source = body.domainBindings[index];
    if (source.parameter || source.kind == DomainBinding::Kind::Parameter)
      return fail("source.finite-domain",
                  "protocol domain capture has an unbound formal", span);
    if (!checker.types.charge(source.children.size(), span))
      return false;
    pending.insert(pending.end(), source.children.begin(),
                   source.children.end());
  }
  std::map<unsigned, unsigned> nodes;
  std::map<unsigned, ValueId> operands;
  // Checked recipes are topologically ordered. Copy the reachable constructor
  // applications, not their runtime results; admission stays at the consumer.
  for (auto index : reachable) {
    const auto &source = body.domainBindings[index];
    if (!checker.types.charge(source.operands.size() + source.children.size() +
                                  source.arguments.size() +
                                  source.argumentOrder.size() + 1,
                              span) ||
        !checker.types.chargeType(source.item, span))
      return false;
    for (const auto &argument : source.arguments)
      if (!checker.types.chargeType(argument, span))
        return false;
    if (source.factory && source.factory->component &&
        !checker.types.chargeType(*source.factory->component, span))
      return false;
    DomainBinding copy = source;
    for (auto &operand : copy.operands) {
      auto found = operands.find(operand.index);
      if (found == operands.end()) {
        auto input = capture(operand);
        if (!input)
          return false;
        found = operands.emplace(operand.index, *input).first;
      }
      operand = found->second;
    }
    for (auto &child : copy.children) {
      auto found = nodes.find(child);
      if (found == nodes.end())
        return fail("source.finite-domain",
                    "captured domain recipe is not topological", span);
      child = found->second;
    }
    nodes.emplace(index, nested.body.domainBindings.size());
    nested.body.domainBindings.push_back(std::move(copy));
  }
  for (auto binding : selected)
    nested.domains.emplace(binding, nodes.at(domains.at(binding)));
  return true;
}
std::optional<unsigned> BodyChecker::domainArgument(uint32_t id,
                                                    unsigned depth) {
  const auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span)) {
    fail("source.limit", "domain argument depth exceeded", expr.span);
    return {};
  }
  if (expr.kind == Expression::Kind::DomainProduct) {
    std::vector<unsigned> children;
    for (auto child : expr.children) {
      auto domain = domainArgument(child, depth + 1);
      if (!domain)
        return {};
      children.push_back(*domain);
    }
    DomainBinding product{DomainBinding::Kind::Product,
                          inference->domainItems.at(id),
                          {},
                          std::move(children),
                          0,
                          {},
                          expr.span};
    product.expression = id;
    auto index = body.domainBindings.size();
    body.domainBindings.push_back(std::move(product));
    return index;
  }
  if (expr.kind == Expression::Kind::Name && expr.binding) {
    auto found = domains.find(*expr.binding);
    if (found != domains.end())
      return found->second;
  }
  if (inference->collectionDomains.count(id)) {
    auto value = expression(id, {}, depth + 1);
    if (!value || !use(*value, expr.span) ||
        !checker.types.charge(1, expr.span))
      return {};
    body.expressionValues.insert_or_assign(id, *value);
    return collectionDomain(checker.types, body.values[value->index].type,
                            *value, body.domainBindings, id, expr.span);
  }
  const auto &target = inference->callees.at(id);
  const auto &callee = checker.output.declarations[target.declaration.index];
  const auto &arguments = inference->arguments.at(id);
  const auto &order = inference->inputs.at(id);
  std::vector<ValueId> operands(callee.inputs.size());
  std::vector<unsigned> domainArguments(callee.domainInputs.size());
  // Only ordinary operands execute here. Composite admission stays at the
  // finite consumer after its initial state and callback snapshots execute.
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto slot = callee.inputOrder[order[i]];
    auto child = expr.children[i];
    if (slot.kind == Declaration::InputSlot::Kind::Domain) {
      auto value = domainArgument(child, depth + 1);
      if (!value)
        return {};
      domainArguments[slot.index] = *value;
    } else {
      auto value = expression(child, {}, depth + 1);
      if (!value || !use(*value, expr.span))
        return {};
      body.expressionValues.insert_or_assign(child, *value);
      operands[slot.index] = *value;
    }
  }
  return instantiateDomain(checker.types, callee, target, arguments, operands,
                           domainArguments, order, body.domainBindings, id,
                           expr.span);
}
} // namespace zkc::language::detail
