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
std::optional<unsigned> BodyChecker::domainArgument(uint32_t id,
                                                    unsigned depth) {
  const auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span)) {
    fail("source.limit", "domain argument depth exceeded", expr.span);
    return {};
  }
  if (expr.kind == Expression::Kind::Name && expr.binding) {
    auto found = domains.find(*expr.binding);
    if (found != domains.end())
      return found->second;
    fail("source.finite-domain", "unavailable finite domain binding",
         expr.span);
    return {};
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
      operands[slot.index] = *value;
    }
  }
  return instantiateDomain(checker.types, callee, target, arguments, operands,
                           domainArguments, order, body.domainBindings, id,
                           expr.span);
}
} // namespace zkc::language::detail
