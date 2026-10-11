#include "DomainClosure.h"
#include "ValueOrigins.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
namespace {
class Closure {
  Semantics &types;
  ArrayRef<Declaration> declarations;
  const Body &body;
  const Substitution &statics;
  ArrayRef<DomainEnvironment> environment;
  DomainShape shape;
  std::vector<ValueId> operands;
  std::map<ValueOrigin, unsigned> inputs;
  ValueOrigins origins;
  struct Context {
    ArrayRef<DomainBinding> nodes;
    std::vector<ValueId> data;
    std::vector<unsigned> domains;
    Substitution statics;
    std::map<unsigned, unsigned> memo;
    std::set<unsigned> active;
    bool external = false;
  };
  bool refuse(Span span, StringRef message) {
    return types.fail("source.finite-domain", message, span);
  }
  bool bounded(unsigned depth, Span span) {
    if (depth > types.work.limits.callDepth)
      return types.fail("source.limit", "finite domain closure depth", span);
    return types.charge(1, span);
  }
  std::optional<Type> type(const Type &source, const Substitution &subst,
                           Span span) {
    auto result = types.substitute(source, subst, span);
    if (result && types.symbolic(*result)) {
      refuse(span, "unresolved finite domain type");
      return {};
    }
    return result;
  }
  std::optional<ValueId> input(ValueId value, Span span) {
    auto identity = origins.get(value, span);
    if (!identity)
      return {};
    auto found = inputs.find(*identity);
    auto closed = type(body.values[value.index].type, statics, span);
    if (!closed)
      return {};
    if (found != inputs.end()) {
      if (shape.inputs[found->second] != *closed) {
        refuse(span, "one domain operand identity has different types");
        return {};
      }
      return ValueId{found->second};
    }
    auto permissions = types.permissions(*closed, span);
    if (!permissions || !permissions->copy || !permissions->drop) {
      if (!types.diagnostic)
        refuse(span, "domain operands require Copy and Drop");
      return {};
    }
    unsigned index = operands.size();
    inputs.emplace(std::move(*identity), index);
    operands.push_back(value);
    shape.inputs.push_back(std::move(*closed));
    return ValueId{index};
  }
  std::optional<unsigned> embed(const DomainEnvironment &selected,
                                unsigned depth) {
    if (!selected.shape ||
        selected.operands.size() != selected.shape->inputs.size() ||
        selected.shape->result >= selected.shape->nodes.size()) {
      refuse({}, "invalid closed domain environment");
      return {};
    }
    // An inherited descriptor contains already-closed constructors. Its operand
    // references are relative to its own data ports, not this caller's SSA.
    Context context{selected.shape->nodes, selected.operands, {}, {}, {}, {}};
    for (unsigned i = 0; i < context.nodes.size(); ++i)
      if (!node(context, i, depth + 1))
        return {};
    return context.memo.at(selected.shape->result);
  }
  std::optional<unsigned>
  application(Context &context, const DomainBinding &binding, unsigned depth) {
    if (!binding.factory ||
        binding.factory->declaration.index >= declarations.size()) {
      refuse(binding.span, "invalid domain factory reference");
      return {};
    }
    auto target = binding.factory->declaration;
    std::vector<Type> arguments;
    for (const auto &argument : binding.arguments) {
      auto closed = type(argument, context.statics, binding.span);
      if (!closed)
        return {};
      arguments.push_back(*closed);
    }
    if (binding.factory->component) {
      auto componentType =
          type(*binding.factory->component, context.statics, binding.span);
      if (!componentType)
        return {};
      const auto *component = types.typeDeclaration(*componentType);
      const auto &abstract = declarations[target.index];
      if (!component || component->kind != Declaration::Kind::Component ||
          !abstract.parent ||
          !types.charge(component->members.size(), binding.span)) {
        if (!types.diagnostic)
          refuse(binding.span,
                 "domain factory dispatch needs a concrete component");
        return {};
      }
      auto selected = llvm::find_if(component->members, [&](DeclarationId id) {
        return declarations[id.index].name == abstract.name;
      });
      const auto inherited =
          declarations[abstract.parent->index].parameters.size();
      if (selected == component->members.end() ||
          arguments.size() < inherited) {
        refuse(binding.span, "domain factory component member differs");
        return {};
      }
      target = *selected;
      auto own = ArrayRef(arguments).drop_front(inherited).vec();
      arguments = componentType->arguments;
      arguments.insert(arguments.end(), own.begin(), own.end());
    }
    const auto &callee = declarations[target.index];
    if (callee.kind != Declaration::Kind::DomainFunction || callee.abstract ||
        !callee.domainDefinition ||
        binding.operands.size() != callee.inputs.size() ||
        binding.children.size() != callee.domainInputs.size() ||
        !types.checkArguments(callee, arguments, binding.span)) {
      if (!types.diagnostic)
        refuse(binding.span, "domain factory has no concrete typed recipe");
      return {};
    }
    const auto &definition = *callee.domainDefinition;
    Context nested{definition.bindings,
                   {},
                   {},
                   types.substitution(callee, arguments),
                   {},
                   {}};
    if (callee.parent && declarations[callee.parent->index].kind ==
                             Declaration::Kind::Component) {
      const auto &component = declarations[callee.parent->index];
      Type self(Type::Kind::Component, component.qualifiedName);
      self.arguments.assign(arguments.begin(),
                            arguments.begin() + component.parameters.size());
      if (component.implementation)
        nested.statics.emplace("self:" + component.implementation->domain,
                               std::move(self));
    }
    for (auto operand : binding.operands) {
      if (operand.index >= context.data.size()) {
        refuse(binding.span, "factory operand mapping differs");
        return {};
      }
      nested.data.push_back(context.data[operand.index]);
    }
    nested.domains.resize(binding.children.size());
    if (binding.argumentOrder.size() != callee.inputOrder.size()) {
      refuse(binding.span, "factory authored argument order differs");
      return {};
    }
    std::vector<bool> assigned(callee.inputOrder.size());
    for (auto parameter : binding.argumentOrder) {
      if (parameter >= assigned.size() || assigned[parameter]) {
        refuse(binding.span, "invalid factory authored argument mapping");
        return {};
      }
      assigned[parameter] = true;
      const auto &slot = callee.inputOrder[parameter];
      if (slot.kind != Declaration::InputSlot::Kind::Domain)
        continue;
      auto selected = node(context, binding.children[slot.index], depth + 1);
      if (!selected)
        return {};
      nested.domains[slot.index] = *selected;
    }
    // The complete selected recipe is the admission boundary, including nodes
    // not used to enumerate its result. All constructor edges remain explicit.
    for (unsigned i = 0; i < nested.nodes.size(); ++i)
      if (!node(nested, i, depth + 1))
        return {};
    if (definition.result >= nested.nodes.size()) {
      refuse(binding.span, "factory result mapping differs");
      return {};
    }
    return nested.memo.at(definition.result);
  }
  std::optional<unsigned> node(Context &context, unsigned index,
                               unsigned depth) {
    if (!bounded(depth, {}))
      return {};
    if (index >= context.nodes.size()) {
      refuse({}, "domain constructor edge outside recipe");
      return {};
    }
    if (auto found = context.memo.find(index); found != context.memo.end())
      return found->second;
    const auto &binding = context.nodes[index];
    if (!context.active.insert(index).second) {
      refuse(binding.span, "cyclic finite domain recipe");
      return {};
    }
    if (!types.charge(binding.operands.size() + binding.children.size() +
                          binding.arguments.size() +
                          binding.argumentOrder.size() + 1,
                      binding.span))
      return {};
    std::optional<unsigned> result;
    if (binding.kind == DomainBinding::Kind::Parameter) {
      if (!binding.parameter || *binding.parameter >= context.domains.size()) {
        refuse(binding.span, "unbound finite domain parameter");
        return {};
      }
      auto &selected = context.domains[*binding.parameter];
      if (context.external &&
          selected == std::numeric_limits<unsigned>::max()) {
        auto closed = embed(environment[*binding.parameter], depth + 1);
        if (!closed)
          return {};
        selected = *closed;
      }
      result = selected;
    } else if (binding.kind == DomainBinding::Kind::Application)
      result = application(context, binding, depth + 1);
    else {
      auto item = type(binding.item, context.statics, binding.span);
      if (!item)
        return {};
      DomainBinding closed{binding.kind, *item, {},          {},
                           binding.axis, {},    binding.span};
      for (auto operand : binding.operands) {
        if (operand.index >= context.data.size()) {
          refuse(binding.span, "domain operand mapping differs");
          return {};
        }
        auto value = input(context.data[operand.index], binding.span);
        if (!value)
          return {};
        closed.operands.push_back(*value);
      }
      for (auto child : binding.children) {
        auto value = node(context, child, depth + 1);
        if (!value)
          return {};
        closed.children.push_back(*value);
      }
      result = shape.nodes.size();
      shape.nodes.push_back(std::move(closed));
    }
    if (!result)
      return {};
    context.active.erase(index);
    context.memo.emplace(index, *result);
    return result;
  }

public:
  Closure(Semantics &types, ArrayRef<Declaration> declarations,
          const Body &body, const Substitution &statics,
          ArrayRef<DomainEnvironment> environment)
      : types(types), declarations(declarations), body(body), statics(statics),
        environment(environment), origins(types, body) {}
  std::optional<DomainEnvironment> run(unsigned root) {
    if (!types.charge(body.values.size() + body.operations.size() +
                          environment.size(),
                      {}))
      return {};
    Context context{body.domainBindings, {}, {}, statics, {}, {}};
    for (unsigned i = 0; i < body.values.size(); ++i)
      context.data.push_back({i});
    context.domains.resize(environment.size(),
                           std::numeric_limits<unsigned>::max());
    context.external = true;
    auto result = node(context, root, 1);
    if (!result)
      return {};
    shape.result = *result;
    frame(shape.identity, "finite-domain");
    for (const auto &input : shape.inputs) {
      if (!types.chargeType(input, {}))
        return {};
      frame(shape.identity, typeIdentity(input));
    }
    frame(shape.identity, "constructors");
    for (const auto &node : shape.nodes) {
      if (!types.chargeType(node.item, node.span) ||
          !types.charge(node.operands.size() + node.children.size() + 1,
                        node.span))
        return {};
      frame(shape.identity, std::to_string(unsigned(node.kind)));
      frame(shape.identity, typeIdentity(node.item));
      frame(shape.identity, std::to_string(node.axis));
      frame(shape.identity, std::to_string(node.operands.size()));
      for (auto operand : node.operands)
        frame(shape.identity, std::to_string(operand.index));
      frame(shape.identity, std::to_string(node.children.size()));
      for (auto child : node.children)
        frame(shape.identity, std::to_string(child));
    }
    frame(shape.identity, std::to_string(shape.result));
    if (!types.charge(shape.identity.size(), {}))
      return {};
    return DomainEnvironment{std::make_shared<DomainShape>(std::move(shape)),
                             std::move(operands)};
  }
};
} // namespace
std::optional<DomainEnvironment>
closeDomain(Semantics &types, ArrayRef<Declaration> declarations,
            const Body &body, unsigned index, const Substitution &statics,
            ArrayRef<DomainEnvironment> environment) {
  return Closure(types, declarations, body, statics, environment).run(index);
}
} // namespace zkc::language::detail
