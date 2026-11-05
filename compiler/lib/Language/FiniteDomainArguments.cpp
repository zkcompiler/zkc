#include "BodyCheck.h"
#include "DescriptorFactories.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<DescriptorOperands> descriptorOperands(Semantics &types,
                                                     const Body &body,
                                                     ArrayRef<unsigned> roots,
                                                     Span span) {
  DescriptorOperands result;
  std::vector<unsigned> pending(roots.begin(), roots.end());
  std::set<unsigned> seen;
  while (!pending.empty()) {
    auto index = pending.back();
    pending.pop_back();
    if (!types.charge(1, span))
      return {};
    if (!seen.insert(index).second)
      continue;
    if (index >= body.descriptorBindings.size()) {
      types.fail("source.finite-domain", "domain operand edge outside body",
                 span);
      return {};
    }
    const auto &domain = body.descriptorBindings[index];
    if (!types.charge(domain.operands.size() + domain.children.size(), span))
      return {};
    result.parameterized |= domain.kind == DescriptorBinding::Kind::Parameter;
    result.values.insert(result.values.end(), domain.operands.begin(),
                         domain.operands.end());
    for (const auto &child : domain.children)
      pending.push_back(child.node);
  }
  return result;
}
bool BodyChecker::addDomain(BindingId id, const DescriptorParameter &parameter,
                            unsigned formal) {
  if (!checker.types.chargeContract(parameter.contract, parameter.span))
    return false;
  domains.emplace(id, body.descriptorBindings.size());
  body.descriptorBindings.push_back({DescriptorBinding::Kind::Parameter,
                                     parameter.contract,
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
    const auto &domain = body.descriptorBindings[index];
    DescriptorParameter formal{syntax.bindings[binding.index].name,
                               domain.contract, domain.span};
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
    if (index >= body.descriptorBindings.size())
      return fail("source.finite-domain", "captured domain edge outside body",
                  span);
    const auto &source = body.descriptorBindings[index];
    if (source.parameter || source.kind == DescriptorBinding::Kind::Parameter)
      return fail("source.finite-domain",
                  "protocol domain capture has an unbound formal", span);
    if (!checker.types.charge(source.children.size(), span))
      return false;
    for (const auto &child : source.children)
      pending.push_back(child.node);
  }
  std::map<unsigned, unsigned> nodes;
  std::map<unsigned, ValueId> operands;
  // Checked recipes are topologically ordered. Copy the reachable constructor
  // applications, not their runtime results; admission stays at the consumer.
  for (auto index : reachable) {
    const auto &source = body.descriptorBindings[index];
    if (!checker.types.charge(source.operands.size() + source.children.size() +
                                  source.arguments.size() +
                                  source.argumentOrder.size() + 1,
                              span) ||
        !checker.types.chargeContract(source.contract, span))
      return false;
    for (const auto &edge : source.children)
      if (!checker.types.chargeContract(edge.contract, span))
        return false;
    for (const auto &argument : source.arguments)
      if (!checker.types.chargeType(argument, span))
        return false;
    if (source.factory && source.factory->module &&
        !checker.types.chargeType(*source.factory->module, span))
      return false;
    DescriptorBinding copy = source;
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
      auto found = nodes.find(child.node);
      if (found == nodes.end())
        return fail("source.finite-domain",
                    "captured domain recipe is not topological", span);
      child.node = found->second;
    }
    nodes.emplace(index, nested.body.descriptorBindings.size());
    nested.body.descriptorBindings.push_back(std::move(copy));
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
    std::vector<DescriptorEdge> children;
    for (auto child : expr.children) {
      auto domain = domainArgument(child, depth + 1);
      if (!domain)
        return {};
      children.push_back({*domain, body.descriptorBindings[*domain].contract});
    }
    DescriptorBinding product{
        DescriptorBinding::Kind::Product,
        *descriptorContract(inference->descriptorTypes.at(id)),
        {},
        std::move(children),
        0,
        {},
        expr.span};
    product.expression = id;
    auto index = body.descriptorBindings.size();
    body.descriptorBindings.push_back(std::move(product));
    return index;
  }
  if (expr.kind == Expression::Kind::Name && expr.binding) {
    auto found = domains.find(*expr.binding);
    if (found != domains.end()) {
      auto retained =
          descriptorOperands(checker.types, body, {found->second}, expr.span);
      if (!retained)
        return {};
      for (auto operand : retained->values)
        if (operand.index >= body.values.size() || !use(operand, expr.span))
          return {};
      return found->second;
    }
  }
  if (inference->collectionDomains.count(id)) {
    auto value = expression(id, {}, depth + 1);
    if (!value)
      return {};
    if (product(*value)) {
      fail("source.finite-domain",
           "ordinary finite domains cannot capture a distributed product",
           expr.span);
      return {};
    }
    if (!use(*value, expr.span) || !checker.types.charge(1, expr.span))
      return {};
    body.expressionValues.insert_or_assign(id, *value);
    return collectionDomain(checker.types, body.values[value->index].type,
                            *value, body.descriptorBindings, id, expr.span);
  }
  const auto &target = inference->callees.at(id);
  const auto &callee = checker.output.declarations[target.declaration.index];
  const auto &arguments = inference->arguments.at(id);
  const auto &order = inference->inputs.at(id);
  std::vector<ValueId> operands(callee.inputs.size());
  std::vector<unsigned> descriptorArguments(callee.descriptorInputs.size());
  // Only ordinary operands execute here. Composite admission stays at the
  // finite consumer after its initial state and callback snapshots execute.
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto slot = callee.inputOrder[order[i]];
    auto child = expr.children[i];
    if (slot.kind == Declaration::InputSlot::Kind::Domain) {
      auto value = domainArgument(child, depth + 1);
      if (!value)
        return {};
      descriptorArguments[slot.index] = *value;
    } else {
      auto value = expression(child, {}, depth + 1);
      if (!value)
        return {};
      if (product(*value)) {
        fail("source.finite-domain",
             "ordinary domain operands cannot be distributed products",
             expr.span);
        return {};
      }
      if (!use(*value, expr.span))
        return {};
      body.expressionValues.insert_or_assign(child, *value);
      operands[slot.index] = *value;
    }
  }
  return instantiateDescriptor(checker.types, callee, target, arguments,
                               operands, descriptorArguments, order,
                               body.descriptorBindings, id, expr.span);
}
} // namespace zkc::language::detail
