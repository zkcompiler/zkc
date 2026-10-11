#include "DomainWitness.h"
#include "ValueOrigins.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
namespace {
class DomainCheck {
  Semantics &types;
  ArrayRef<Declaration> declarations;
  const Body &body;
  const Substitution &statics;
  ArrayRef<DomainEnvironment> environment;
  const Body &caller;
  const std::function<ValueId(ValueId)> &map;
  const DomainShape &candidate;
  ValueOrigins &origins;
  std::vector<std::optional<ValueId>> ports;
  unsigned next = 0;
  std::vector<unsigned> depths;
  using Factory = std::tuple<unsigned, std::vector<std::string>,
                             std::vector<ValueOrigin>, std::vector<unsigned>>;
  std::map<Factory, unsigned> checkedFactories;
  std::set<Factory> activeFactories;
  struct Context {
    ArrayRef<DomainBinding> bindings;
    std::vector<ValueId> data;
    std::vector<unsigned> domains;
    Substitution statics;
    std::map<unsigned, unsigned> checked;
    std::set<unsigned> active;
    bool external = false;
  };
  bool refuse(Span span, StringRef message) {
    return types.fail("source.domain-witness", message, span);
  }
  std::optional<Type> type(const Type &value, const Substitution &substitution,
                           Span span) {
    auto selected = types.substitute(value, substitution, span);
    if (selected && types.symbolic(*selected)) {
      refuse(span, "domain witness contains an unresolved type");
      return {};
    }
    return selected;
  }
  bool bindPort(unsigned index, ValueId value, Span span) {
    if (index >= ports.size() || value.index >= caller.values.size())
      return refuse(span,
                    "descriptor operand mapping is outside its input space");
    auto actual = type(caller.values[value.index].type, statics, span);
    auto permissions = actual ? types.permissions(*actual, span) : std::nullopt;
    if (!actual || !permissions || !permissions->copy || !permissions->drop ||
        *actual != candidate.inputs[index])
      return types.diagnostic ? false
                              : refuse(span, "descriptor operand type differs");
    if (ports[index]) {
      auto expected = origins.get(*ports[index], span),
           provided = origins.get(value, span);
      if (!expected || !provided || *expected != *provided)
        return types.diagnostic
                   ? false
                   : refuse(span, "descriptor merges distinct source operands");
    } else
      ports[index] = value;
    return true;
  }
  std::optional<unsigned> constructor(const DomainBinding &source,
                                      const Substitution &substitution,
                                      ArrayRef<ValueId> data,
                                      ArrayRef<unsigned> children) {
    if (next >= candidate.nodes.size()) {
      refuse(source.span, "descriptor omits an admitted constructor");
      return {};
    }
    const auto &actual = candidate.nodes[next];
    if (!types.chargeType(actual.item, source.span) ||
        !types.charge(actual.operands.size() + actual.children.size() + 1,
                      source.span))
      return {};
    auto item = type(source.item, substitution, source.span);
    if (!item || source.kind != actual.kind || *item != actual.item ||
        source.axis != actual.axis || data.size() != actual.operands.size() ||
        children != ArrayRef(actual.children) || actual.factory ||
        actual.parameter || actual.expression || !actual.arguments.empty() ||
        !actual.argumentOrder.empty()) {
      if (!types.diagnostic)
        refuse(source.span, "admitted constructor differs from checked source");
      return {};
    }
    for (unsigned i = 0; i < data.size(); ++i)
      if (!bindPort(actual.operands[i].index, data[i], source.span))
        return {};
    unsigned depth = 1;
    for (auto child : children) {
      if (child >= next) {
        refuse(source.span, "constructor child does not precede its use");
        return {};
      }
      depth = std::max(depth, depths[child] + 1);
    }
    if (depth > 63) {
      types.fail("source.limit",
                 "descriptor constructor depth exceeds its bound", source.span);
      return {};
    }
    depths.push_back(depth);
    return next++;
  }
  std::optional<unsigned> inherited(const DomainEnvironment &expected,
                                    unsigned depth) {
    if (!expected.shape ||
        expected.operands.size() != expected.shape->inputs.size() ||
        expected.shape->result >= expected.shape->nodes.size()) {
      refuse({}, "invalid inherited domain witness");
      return {};
    }
    if (!types.charge(
            expected.shape->nodes.size() + expected.operands.size() + 1, {}))
      return {};
    for (unsigned i = 0; i < expected.operands.size(); ++i) {
      auto value = expected.operands[i];
      if (value.index >= caller.values.size()) {
        refuse({}, "inherited operand is outside the current body");
        return {};
      }
      auto actual = type(caller.values[value.index].type, statics, {});
      if (!actual || *actual != expected.shape->inputs[i]) {
        if (!types.diagnostic)
          refuse({}, "inherited operand type differs");
        return {};
      }
    }
    Context context{expected.shape->nodes, expected.operands, {}, {}, {}, {}};
    for (unsigned i = 0; i < context.bindings.size(); ++i) {
      const auto &binding = context.bindings[i];
      if (binding.kind == DomainBinding::Kind::Parameter ||
          binding.kind == DomainBinding::Kind::Application) {
        refuse(binding.span, "inherited descriptor is not closed");
        return {};
      }
      if (!node(context, i, depth + 1))
        return {};
    }
    return context.checked.at(expected.shape->result);
  }
  std::optional<unsigned>
  application(Context &context, const DomainBinding &binding, unsigned depth) {
    if (!binding.factory ||
        binding.factory->declaration.index >= declarations.size()) {
      refuse(binding.span, "source factory reference is invalid");
      return {};
    }
    auto target = binding.factory->declaration;
    std::vector<Type> arguments;
    for (const auto &argument : binding.arguments) {
      auto value = type(argument, context.statics, binding.span);
      if (!value)
        return {};
      arguments.push_back(*value);
    }
    if (binding.factory->module) {
      auto module =
          type(*binding.factory->module, context.statics, binding.span);
      if (!module)
        return {};
      const auto *owner = types.typeDeclaration(*module);
      const auto &abstract = declarations[target.index];
      if (!owner || owner->kind != Declaration::Kind::Module ||
          !abstract.parent ||
          !types.charge(owner->members.size(), binding.span)) {
        if (!types.diagnostic)
          refuse(binding.span, "factory module selection differs");
        return {};
      }
      auto member = llvm::find_if(owner->members, [&](DeclarationId id) {
        return declarations[id.index].name == abstract.name;
      });
      unsigned inherited =
          declarations[abstract.parent->index].parameters.size();
      if (member == owner->members.end() || arguments.size() < inherited) {
        refuse(binding.span, "factory member selection differs");
        return {};
      }
      auto own = ArrayRef(arguments).drop_front(inherited).vec();
      target = *member;
      arguments = module->arguments;
      arguments.insert(arguments.end(), own.begin(), own.end());
    }
    const auto &callee = declarations[target.index];
    if (callee.kind != Declaration::Kind::DomainFunction || callee.abstract ||
        !callee.domainDefinition ||
        binding.operands.size() != callee.inputs.size() ||
        binding.children.size() != callee.domainInputs.size() ||
        !types.checkArguments(callee, arguments, binding.span)) {
      if (!types.diagnostic)
        refuse(binding.span, "factory has no checked concrete definition");
      return {};
    }
    const auto &definition = *callee.domainDefinition;
    Context nested{definition.bindings,
                   {},
                   {},
                   types.substitution(callee, arguments),
                   {},
                   {}};
    if (callee.parent &&
        declarations[callee.parent->index].kind == Declaration::Kind::Module) {
      const auto &owner = declarations[callee.parent->index];
      Type self(Type::Kind::Module, owner.qualifiedName);
      self.arguments.assign(arguments.begin(),
                            arguments.begin() + owner.parameters.size());
      if (owner.implementation)
        nested.statics.emplace("self:" + owner.implementation->domain,
                               std::move(self));
    }
    Factory identity;
    std::get<0>(identity) = target.index;
    for (const auto &argument : arguments) {
      if (!types.chargeType(argument, binding.span))
        return {};
      std::get<1>(identity).push_back(typeIdentity(argument));
    }
    for (auto operand : binding.operands) {
      if (operand.index >= context.data.size()) {
        refuse(binding.span, "factory data port mapping differs");
        return {};
      }
      auto value = context.data[operand.index];
      nested.data.push_back(value);
      auto origin = origins.get(value, binding.span);
      if (!origin)
        return {};
      std::get<2>(identity).push_back(std::move(*origin));
    }
    if (binding.argumentOrder.size() != callee.inputOrder.size()) {
      refuse(binding.span, "factory argument order coverage differs");
      return {};
    }
    nested.domains.resize(binding.children.size());
    std::vector<bool> assigned(callee.inputOrder.size());
    for (auto argument : binding.argumentOrder) {
      if (argument >= assigned.size() || assigned[argument]) {
        refuse(binding.span, "factory named argument mapping differs");
        return {};
      }
      assigned[argument] = true;
      const auto &slot = callee.inputOrder[argument];
      if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        auto selected = node(context, binding.children[slot.index], depth + 1);
        if (!selected)
          return {};
        nested.domains[slot.index] = *selected;
      }
    }
    std::get<3>(identity) = nested.domains;
    uint64_t width = nested.domains.size() + 1, levels = 1;
    for (const auto &argument : std::get<1>(identity))
      width += argument.size() + 1;
    for (const auto &origin : std::get<2>(identity))
      width += origin.second.size() + 1;
    for (auto count = checkedFactories.size() + activeFactories.size();
         count > 1; count >>= 1)
      ++levels;
    if (!types.charge(width * levels * 3, binding.span))
      return {};
    if (auto found = checkedFactories.find(identity);
        found != checkedFactories.end())
      return found->second;
    if (!activeFactories.insert(identity).second) {
      refuse(binding.span, "cyclic source factory selection");
      return {};
    }
    for (unsigned i = 0; i < nested.bindings.size(); ++i)
      if (!node(nested, i, depth + 1))
        return {};
    if (definition.result >= nested.bindings.size()) {
      refuse(binding.span, "factory result is outside its recipe");
      return {};
    }
    auto result = nested.checked.at(definition.result);
    activeFactories.erase(identity);
    checkedFactories.emplace(std::move(identity), result);
    return result;
  }
  std::optional<unsigned> node(Context &context, unsigned index,
                               unsigned depth) {
    if (depth > types.work.limits.callDepth) {
      types.fail("source.limit", "domain witness closure depth exceeded", {});
      return {};
    }
    if (!types.charge(1, {}))
      return {};
    if (index >= context.bindings.size()) {
      refuse({}, "source domain edge is outside its recipe");
      return {};
    }
    if (auto found = context.checked.find(index);
        found != context.checked.end())
      return found->second;
    const auto &binding = context.bindings[index];
    if (!context.active.insert(index).second) {
      refuse(binding.span, "cyclic source domain edge");
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
        refuse(binding.span, "unbound domain parameter in witness");
        return {};
      }
      auto &selected = context.domains[*binding.parameter];
      if (context.external &&
          selected == std::numeric_limits<unsigned>::max()) {
        auto actual = inherited(environment[*binding.parameter], depth + 1);
        if (!actual)
          return {};
        selected = *actual;
      }
      result = selected;
    } else if (binding.kind == DomainBinding::Kind::Application)
      result = application(context, binding, depth);
    else {
      std::vector<ValueId> data;
      std::vector<unsigned> children;
      for (auto operand : binding.operands) {
        if (operand.index >= context.data.size()) {
          refuse(binding.span, "constructor data edge differs");
          return {};
        }
        data.push_back(context.data[operand.index]);
      }
      for (auto child : binding.children) {
        auto selected = node(context, child, depth + 1);
        if (!selected)
          return {};
        children.push_back(*selected);
      }
      result = constructor(binding, context.statics, data, children);
    }
    if (!result)
      return {};
    auto expected = type(binding.item, context.statics, binding.span);
    if (!expected || *expected != candidate.nodes[*result].item) {
      if (!types.diagnostic)
        refuse(binding.span, "domain result item differs");
      return {};
    }
    context.active.erase(index);
    context.checked.emplace(index, *result);
    return result;
  }

public:
  DomainCheck(Semantics &types, ArrayRef<Declaration> declarations,
              const Body &body, const Body &caller,
              const std::function<ValueId(ValueId)> &map,
              const Substitution &statics,
              ArrayRef<DomainEnvironment> environment,
              const DomainShape &candidate, ValueOrigins &origins)
      : types(types), declarations(declarations), body(body), statics(statics),
        environment(environment), caller(caller), map(map),
        candidate(candidate), origins(origins) {}
  bool run(unsigned root) {
    if (candidate.result >= candidate.nodes.size())
      return refuse({}, "invalid descriptor witness shape");
    if (candidate.inputs.size() > 1024 || candidate.nodes.size() > 4095)
      return types.fail("source.limit",
                        "descriptor witness exceeds formation bounds", {});
    if (!types.charge(body.values.size() + candidate.inputs.size() +
                          candidate.nodes.size() + 1,
                      {}))
      return false;
    for (const auto &input : candidate.inputs)
      if (!types.chargeType(input, {}))
        return false;
    ports.resize(candidate.inputs.size());
    Context context{body.domainBindings, {}, {}, statics, {}, {}};
    for (unsigned i = 0; i < body.values.size(); ++i)
      context.data.push_back(map({i}));
    context.domains.resize(environment.size(),
                           std::numeric_limits<unsigned>::max());
    context.external = true;
    auto selected = node(context, root, 1);
    if (!selected || *selected != candidate.result ||
        next != candidate.nodes.size())
      return types.diagnostic
                 ? false
                 : refuse({},
                          "descriptor admission or result coverage differs");
    std::set<ValueOrigin> distinct;
    for (auto input : ports) {
      if (!input)
        return refuse({}, "descriptor has an unbound data input");
      auto origin = origins.get(*input);
      if (!origin)
        return false;
      if (!distinct.insert(std::move(*origin)).second)
        return refuse(
            {}, "descriptor repeats one source operand as distinct inputs");
    }
    return true;
  }
  std::vector<ValueId> inputs() const {
    std::vector<ValueId> result;
    for (auto input : ports)
      result.push_back(*input);
    return result;
  }
};
} // namespace
std::optional<std::vector<ValueId>>
bindDomainInputs(Semantics &types, ArrayRef<Declaration> declarations,
                 const Body &source, const Body &caller,
                 const std::function<ValueId(ValueId)> &map, unsigned root,
                 const Substitution &statics,
                 ArrayRef<DomainEnvironment> environment,
                 const DomainShape &candidate, ValueOrigins *cache) {
  ValueOrigins localOrigins(types, caller);
  auto &origins = cache ? *cache : localOrigins;
  if (!origins.describes(caller)) {
    types.fail("source.domain-witness",
               "origin cache belongs to a different body", {});
    return {};
  }
  DomainCheck check(types, declarations, source, caller, map, statics,
                    environment, candidate, origins);
  if (!check.run(root))
    return {};
  return check.inputs();
}
bool checkDomainClosure(Semantics &types, ArrayRef<Declaration> declarations,
                        const Body &body, unsigned root,
                        const Substitution &statics,
                        ArrayRef<DomainEnvironment> environment,
                        const DomainEnvironment &candidate,
                        ValueOrigins *cache) {
  if (!candidate.shape ||
      candidate.operands.size() != candidate.shape->inputs.size())
    return types.fail("source.domain-witness",
                      "invalid descriptor operand coverage", {});
  ValueOrigins localOrigins(types, body);
  auto &origins = cache ? *cache : localOrigins;
  auto inputs = bindDomainInputs(
      types, declarations, body, body, [](ValueId value) { return value; },
      root, statics, environment, *candidate.shape, &origins);
  if (!inputs)
    return false;
  for (unsigned i = 0; i < inputs->size(); ++i) {
    auto expected = origins.get((*inputs)[i]),
         actual = origins.get(candidate.operands[i]);
    if (!expected || !actual || *expected != *actual)
      return types.diagnostic
                 ? false
                 : types.fail("source.domain-witness",
                              "descriptor caller operand differs", {});
  }
  return true;
}
} // namespace zkc::language::detail
