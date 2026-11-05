#include "BodyCheck.h"
#include "ScopedWitness.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<ValueId>>
BodyChecker::application(const Expression &expr) {
  if (!protocol()) {
    fail("source.mode", "protocol application requires protocol mode",
         expr.span);
    return {};
  }
  const auto id = uint32_t(&expr - syntax.expressions.data());
  TypeScope types(*this, id, {});
  if (!types)
    return {};
  const auto &target = inference->callees.at(id);
  auto &callee = checker.output.declarations[target.declaration.index];
  if (callee.kind != Declaration::Kind::Protocol) {
    fail("source.call", "application target must be a protocol", expr.span);
    return {};
  }
  if (callee.completes) {
    fail("source.completion",
         "a completing protocol can only be selected as an Entry", expr.span);
    return {};
  }
  const bool method = expr.kind == Expression::Kind::MethodCall;
  if (method && expr.roles) {
    fail("source.roles", "method roles must come from the receiver", expr.span);
    return {};
  }
  const auto &roleNames = expr.roles ? *expr.roles : callee.roles;
  if (!method && roleNames.size() != callee.roles.size()) {
    fail("source.roles",
         "protocol role substitution must cover the callee roster", expr.span);
    return {};
  }
  std::vector<unsigned> mapping;
  std::optional<ValueId> receiver;
  const auto &arguments = inference->arguments.at(id);
  auto substitution = checker.types.substitution(callee, arguments);
  if (target.module && callee.parent)
    substitution.emplace(
        "self:" +
            checker.output.declarations[callee.parent->index].qualifiedName,
        *target.module);
  if (method) {
    const auto &port = callee.inputs.front();
    auto type = checker.types.substitute(port.type, substitution, expr.span);
    if (!type)
      return {};
    receiver = expression(expr.children.front(), *type);
    if (!receiver)
      return {};
    std::vector<std::optional<unsigned>> roles(callee.roles.size());
    if (type->kind == Type::Kind::LogicalRecord && port.placement &&
        std::holds_alternative<ProductPlacement>(port.placement->value)) {
      // A nominal product retains the declaration's ordered role telescope.
      // Its availability union cannot recover this correspondence, including
      // roles whose fields are empty or absent from physical storage.
      const auto &actualPlacement = body.values[receiver->index].placement;
      if (!actualPlacement ||
          !std::holds_alternative<ProductPlacement>(actualPlacement->value)) {
        fail("source.roles", "receiver has no exact nominal role map",
             expr.span);
        return {};
      }
      const auto &formal = std::get<ProductPlacement>(port.placement->value);
      const auto &actual = std::get<ProductPlacement>(actualPlacement->value);
      if (formal.arguments.size() != actual.arguments.size()) {
        fail("source.roles", "receiver nominal role arity differs", expr.span);
        return {};
      }
      if (!checker.types.charge(formal.arguments.size() + roles.size() + 1,
                                expr.span))
        return {};
      for (unsigned i = 0; i < formal.arguments.size(); ++i)
        roles[formal.arguments[i]] = actual.arguments[i];
    } else {
      // Direct families distinguish the holder and one receiver. A plain
      // availability set with several members carries no ordered role map.
      auto actual = placement->resolve(components(*receiver));
      auto formal = port.roles;
      if (!checker.types.charge(
              actual.size() + formal.size() + roles.size() + 1, expr.span))
        return {};
      if (port.oracle) {
        auto holder = body.values[receiver->index].oracleHolder;
        if (!holder || !llvm::is_contained(actual, *holder) ||
            !llvm::is_contained(formal, port.oracle->holder)) {
          fail("source.roles", "receiver has no exact method holder",
               expr.span);
          return {};
        }
        roles[port.oracle->holder] = *holder;
        llvm::erase(formal, port.oracle->holder);
        llvm::erase(actual, *holder);
      }
      if (formal.size() != actual.size() || formal.size() > 1) {
        fail("source.roles",
             "receiver method role correspondence is not unique", expr.span);
        return {};
      }
      if (formal.size() == 1)
        roles[formal.front()] = actual.front();
    }
    for (auto role : roles) {
      if (!role || llvm::is_contained(mapping, *role)) {
        fail("source.roles", "receiver must determine every method role",
             expr.span);
        return {};
      }
      if (!active({*role}, expr.span))
        return {};
      mapping.push_back(*role);
    }
  }
  if (!method) {
    auto resolvedRoles = checker.roleArguments(decl, roleNames, expr.span);
    if (!resolvedRoles)
      return {};
    mapping = std::move(*resolvedRoles);
    for (auto role : mapping)
      if (!active({role}, expr.span))
        return {};
  }
  auto mappedRoles = [&](const Port &port) {
    std::vector<unsigned> roles;
    for (auto role : port.roles)
      roles.push_back(mapping[role]);
    llvm::sort(roles);
    return roles;
  };
  const auto &binding = inference->inputs.at(id);
  std::vector<ValueId> operands(callee.inputs.size());
  std::vector<ServiceId> managed(callee.services.size());
  // Evaluate authored operands in source order; inputOrder identifies the
  // destination independently of that order, including managed services.
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto child = expr.children[i];
    const auto &slot = callee.inputOrder[binding[i]];
    if (slot.kind == Declaration::InputSlot::Kind::Service) {
      auto root = service(syntax.expressions[child]);
      if (!root)
        return {};
      const auto &actual = body.services[root->index];
      const auto &expected = callee.services[slot.index];
      auto field =
          checker.types.substitute(expected.field, substitution, expr.span);
      if (!field)
        return {};
      if (*field != actual.field || mapping[expected.owner] != actual.owner) {
        fail("source.service", "managed service field or mapped owner differs",
             expr.span);
        return {};
      }
      managed[slot.index] = *root;
    } else {
      const auto &port = callee.inputs[slot.index];
      auto type = checker.types.substitute(port.type, substitution, expr.span);
      if (!type)
        return {};
      std::optional<ValuePlacement> expectedPlacement;
      if (port.placement) {
        auto specialized = checker.types.placement(
            *type, *port.placement, callee.roles.size(), expr.span);
        if (!specialized)
          return {};
        expectedPlacement = checker.types.remapPlacement(
            *specialized, mapping, decl.roles.size(), expr.span);
        if (!expectedPlacement)
          return {};
        expectedPlacement = checker.types.placement(
            *type, *expectedPlacement, decl.roles.size(), expr.span);
        if (!expectedPlacement)
          return {};
      }
      auto value = method && i == 0
                       ? receiver
                       : expression(child, *type, 1, false, expectedPlacement);
      if (!value ||
          (method && i == 0 && expectedPlacement &&
           !matchPlacement(*value, *expectedPlacement, expr.span)) ||
          (!expectedPlacement &&
           !demand(*value, mappedRoles(port), expr.span)) ||
          !use(*value, expr.span))
        return {};
      if (port.oracle && body.values[value->index].oracleHolder !=
                             mapping[port.oracle->holder]) {
        fail("source.oracle-role",
             "oracle argument holder differs from mapped port", expr.span);
        return {};
      }
      if (!port.placement && type->kind == Type::Kind::LogicalRecord &&
          components(*value).roles != mappedRoles(port)) {
        fail("source.oracle-role",
             "logical record argument must retain its complete role family",
             expr.span);
        return {};
      }
      operands[slot.index] = *value;
    }
  }
  std::vector<Value> results;
  for (const auto &port : callee.outputs) {
    auto type = checker.types.substitute(port.type, substitution, expr.span);
    if (!type)
      return {};
    std::optional<ValuePlacement> placed;
    if (port.placement) {
      auto specialized = checker.types.placement(
          *type, *port.placement, callee.roles.size(), expr.span);
      if (!specialized)
        return {};
      placed = checker.types.remapPlacement(*specialized, mapping,
                                            decl.roles.size(), expr.span);
      if (!placed)
        return {};
      placed =
          checker.types.placement(*type, *placed, decl.roles.size(), expr.span);
      if (!placed)
        return {};
    }
    results.push_back({*type, mappedRoles(port), expr.span,
                       port.oracle ? std::optional(mapping[port.oracle->holder])
                                   : std::nullopt,
                       std::move(placed)});
  }
  auto emitted = emitResults(
      ProtocolApplication{callee.id, operands, arguments, mapping, managed},
      std::move(results), expr.span);
  if (emitted) {
    CallBinding invocation{target, arguments, operands, {}, {}, {}, {}};
    invocation.argumentOrder = binding;
    invocation.roles = mapping;
    invocation.services = managed;
    invocation.scopedSource = witnesses.calls.size();
    witnesses.calls.push_back(
        std::make_shared<ScopedCallSource>(ScopedCallSource{{decl.id,
                                                             target.declaration,
                                                             id,
                                                             {},
                                                             target.module,
                                                             arguments,
                                                             target.reference},
                                                            scoped,
                                                            domains,
                                                            {}}));
    body.operations.back().binding = std::move(invocation);
    placement->applications.push_back(body.operations.size() - 1);
  }
  return emitted;
}
} // namespace zkc::language::detail
