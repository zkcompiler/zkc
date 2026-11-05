#include "DescriptorClosure.h"
#include "DescriptorFrames.h"
#include "DescriptorSequence.h"
#include "FormationCursor.h"
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
  ArrayRef<DescriptorEnvironment> environment;
  DescriptorShape shape;
  std::shared_ptr<DescriptorArena> arena;
  std::optional<DescriptorSequence> sequences;
  std::vector<ValueId> operands;
  std::map<ValueOrigin, unsigned> inputs;
  ValueOrigins &origins;
  bool sourceJudgment;
  /// Keyed by lookup keys; confined to this one closure pass.
  std::map<std::string, std::pair<unsigned, unsigned>> factories;
  std::set<std::string> activeFactories;
  std::vector<unsigned> constructorDepths;
  // Include the terminal yield in the descriptor operation and depth limits.
  static constexpr unsigned maxInputs = 1024, maxNodes = 4095, maxDepth = 63;
  struct Context {
    ArrayRef<DescriptorBinding> nodes;
    std::vector<ValueId> data;
    std::vector<unsigned> domains;
    Substitution statics;
    std::map<unsigned, unsigned> memo;
    std::set<unsigned> active;
    bool external = false;
    unsigned block = 0;
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
    if (result && !sourceJudgment && types.symbolic(*result)) {
      refuse(span, "unresolved finite domain type");
      return {};
    }
    return result;
  }
  std::optional<DescriptorContract>
  closedContract(const DescriptorContract &source,
                 const Substitution &substitution, Span span) {
    if (descriptorType(source).kind == Type::Kind::Descriptor &&
        !finiteDescriptorItem(source)) {
      refuse(span, "finite closure requires one item contract");
      return {};
    }
    if (!types.chargeContract(source, span))
      return {};
    auto term = type(descriptorType(source), substitution, span);
    if (!term)
      return {};
    auto contract = descriptorContract(*term);
    if (!contract || (term->kind == Type::Kind::Descriptor &&
                      !finiteDescriptorItem(*contract))) {
      refuse(span, "finite closure requires a Finite leaf contract");
      return {};
    }
    return contract;
  }
  std::optional<ValueId> input(ValueId value,
                               const DescriptorContract &contract, Span span) {
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
    if (!sourceJudgment &&
        descriptorType(contract).kind == Type::Kind::Descriptor) {
      auto permissions = types.permissions(*closed, span);
      if (!finiteDescriptorItem(contract) || !permissions ||
          !permissions->copy || !permissions->drop) {
        if (!types.diagnostic)
          refuse(
              span,
              "finite operands require Copy and Drop and one item parameter");
        return {};
      }
    }
    if (operands.size() >= types.work.limits.operations) {
      types.fail("source.limit", "descriptor data input work bound exceeded",
                 span);
      return {};
    }
    unsigned index = operands.size();
    inputs.emplace(std::move(*identity), index);
    operands.push_back(value);
    shape.inputs.push_back(std::move(*closed));
    return ValueId{index};
  }
  std::optional<unsigned> embed(const DescriptorEnvironment &selected,
                                const DescriptorBinding &parameter,
                                Context &context) {
    if (!selected.shape || !selected.shape->arena ||
        selected.operands.size() != selected.shape->inputs.size() ||
        selected.shape->payload >= selected.shape->arena->payloads.size()) {
      refuse(parameter.span, "invalid closed descriptor environment");
      return {};
    }
    const auto &source = *selected.shape;
    const auto &storage = *source.arena;
    if (source.formation >= storage.blocks.size()) {
      refuse(parameter.span, "inherited formation block is absent");
      return {};
    }
    for (unsigned i = 0; i < source.inputs.size(); ++i) {
      if (selected.operands[i].index >= body.values.size()) {
        refuse(parameter.span,
               "inherited descriptor input is outside its Body");
        return {};
      }
      auto actual = type(body.values[selected.operands[i].index].type, statics,
                         parameter.span);
      if (!actual || *actual != source.inputs[i]) {
        if (!types.diagnostic)
          refuse(parameter.span, "inherited descriptor input type differs");
        return {};
      }
    }
    if (finiteDescriptorItem(storage.payloads[source.payload].contract) &&
        (source.inputs.size() > maxInputs || source.nodes.size() > maxNodes)) {
      types.fail("source.limit",
                 "inherited Finite projection exceeds constructor allowance",
                 parameter.span);
      return {};
    }
    // An environment is immutable storage, not an admission certificate.
    if (!checkClosedDescriptorStorage(types, source, parameter.span,
                                      "source.finite-domain"))
      return {};
    if (!FormationCursor(types, storage)
             .walk(
                 source.formation,
                 [&](const DescriptorOccurrence &event) {
                   for (auto child : event.children)
                     if (child >= storage.payloads.size())
                       return refuse(
                           parameter.span,
                           "inherited occurrence child is outside its arena");
                   return true;
                 },
                 false))
      return {};
    if (!types.charge(storage.sequences.size() *
                              sizeof(DescriptorSequenceNode) +
                          storage.payloads.size() * sizeof(DescriptorPayload) +
                          storage.blocks.size() *
                              sizeof(std::vector<DescriptorOccurrence>) +
                          storage.leaves.size() * sizeof(DescriptorBinding),
                      parameter.span))
      return {};
    unsigned leafBase = arena->leaves.size(),
             payloadBase = arena->payloads.size(),
             blockBase = arena->blocks.size(),
             sequenceBase = arena->sequences.size();
    if (storage.sequences.size() > UINT32_MAX - sequenceBase) {
      types.fail("source.limit", "inherited sequence arena overflows",
                 parameter.span);
      return {};
    }
    for (const auto &node : storage.leaves) {
      if (!chargeDescriptorBindingCopy(types, node))
        return {};
      DescriptorBinding copy = node;
      for (auto &value : copy.operands) {
        if (value.index >= selected.operands.size()) {
          refuse(parameter.span, "inherited operand mapping differs");
          return {};
        }
        auto mapped = input(selected.operands[value.index], node.contract,
                            parameter.span);
        if (!mapped)
          return {};
        value = *mapped;
      }
      unsigned depth = 1;
      for (auto &child : copy.children) {
        child.node += leafBase;
        depth = std::max(depth, constructorDepths.at(child.node) + 1);
      }
      constructorDepths.push_back(depth);
      arena->leaves.push_back(std::move(copy));
    }
    for (auto node : storage.sequences) {
      if (node.count)
        for (unsigned i = 0; i < node.count; ++i)
          node.elements[i] += payloadBase;
      else {
        node.left += sequenceBase;
        node.right += sequenceBase;
      }
      arena->sequences.push_back(std::move(node));
    }
    for (const auto &value : storage.payloads) {
      if (!types.chargeContract(value.contract, parameter.span))
        return {};
      if (auto *edges = std::get_if<std::vector<unsigned>>(&value.value))
        if (!types.charge(edges->size() * sizeof(unsigned), parameter.span))
          return {};
      auto copy = value;
      if (auto *leaf = std::get_if<unsigned>(&copy.value))
        *leaf += leafBase;
      else if (auto *product = std::get_if<std::vector<unsigned>>(&copy.value))
        for (auto &edge : *product)
          edge += payloadBase;
      else if (auto &root = std::get<uint64_t>(copy.value); root != UINT32_MAX)
        root += sequenceBase;
      arena->payloads.push_back(std::move(copy));
    }
    for (const auto &sourceBlock : storage.blocks) {
      if (!types.charge(sourceBlock.size() * sizeof(DescriptorOccurrence),
                        parameter.span))
        return {};
      std::vector<DescriptorOccurrence> copy;
      for (const auto &event : sourceBlock) {
        if (!types.charge(event.children.size() * sizeof(unsigned) +
                              event.authority.size(),
                          parameter.span))
          return {};
        auto occurrence = event;
        occurrence.result += payloadBase;
        for (auto &child : occurrence.children)
          child += payloadBase;
        if (occurrence.invocation)
          *occurrence.invocation += blockBase;
        copy.push_back(std::move(occurrence));
      }
      arena->blocks.push_back(std::move(copy));
    }
    unsigned result = payloadBase + source.payload;
    return occurrence(context, parameter, result, {},
                      blockBase + source.formation)
               ? std::optional(result)
               : std::nullopt;
  }
  bool occurrence(Context &context, const DescriptorBinding &binding,
                  unsigned result, std::vector<unsigned> children,
                  std::optional<unsigned> invocation = {}) {
    auto authority =
        descriptorOccurrenceAuthority(types, binding, context.statics);
    if (!authority || !types.charge(sizeof(DescriptorOccurrence) +
                                        children.size() * sizeof(unsigned),
                                    binding.span))
      return false;
    arena->blocks[context.block].push_back({binding.kind, binding.expression,
                                            result, std::move(children),
                                            invocation, std::move(*authority)});
    return true;
  }
  std::optional<unsigned> residual(Context &context,
                                   const DescriptorBinding &binding,
                                   const DescriptorContract &contract,
                                   std::vector<unsigned> children,
                                   std::optional<unsigned> parameter = {}) {
    if (!sourceJudgment ||
        !types.charge(sizeof(DescriptorPayload) + sizeof(DescriptorResidual) +
                          children.size() * sizeof(unsigned),
                      binding.span) ||
        !types.chargeContract(contract, binding.span))
      return {};
    DescriptorResidual open{parameter, {}, children};
    if (!parameter) {
      if (!chargeDescriptorBindingCopy(types, binding) ||
          !types.chargeContract(contract, binding.span))
        return {};
      DescriptorBinding operation = binding;
      operation.contract = contract;
      operation.expression.reset();
      operation.children.clear();
      for (auto &argument : operation.arguments) {
        auto actual = type(argument, context.statics, binding.span);
        if (!actual)
          return {};
        argument = std::move(*actual);
      }
      if (operation.factory && operation.factory->module) {
        auto actual =
            type(*operation.factory->module, context.statics, binding.span);
        if (!actual)
          return {};
        operation.factory->module = std::move(*actual);
      }
      for (auto &operand : operation.operands) {
        if (operand.index >= context.data.size())
          return {};
        auto selected =
            input(context.data[operand.index], contract, binding.span);
        if (!selected)
          return {};
        operand = *selected;
      }
      if (!types.charge(2 * sizeof(void *), binding.span))
        return {};
      open.operation =
          std::make_shared<const DescriptorBinding>(std::move(operation));
    }
    unsigned result = arena->payloads.size();
    arena->payloads.push_back({contract, std::move(open), {}});
    return occurrence(context, binding, result, std::move(children))
               ? std::optional(result)
               : std::nullopt;
  }
  std::optional<unsigned> application(Context &context,
                                      const DescriptorBinding &binding,
                                      unsigned depth) {
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
      arguments.push_back(std::move(*closed));
    }
    if (binding.factory->module) {
      auto componentType =
          type(*binding.factory->module, context.statics, binding.span);
      if (!componentType)
        return {};
      auto selected =
          types.dispatch(*componentType, target, arguments, binding.span);
      if (!selected)
        return {};
      target = selected->declaration;
      arguments = std::move(selected->arguments);
    }
    const auto &callee = declarations[target.index];
    if (callee.kind != Declaration::Kind::View ||
        ((!sourceJudgment || !callee.abstract) &&
         !callee.descriptorDefinition) ||
        binding.operands.size() != callee.inputs.size() ||
        binding.children.size() != callee.descriptorInputs.size() ||
        !types.checkArguments(callee, arguments, binding.span)) {
      if (!types.diagnostic)
        refuse(binding.span, "domain factory has no concrete typed recipe");
      return {};
    }
    if (sourceJudgment && callee.abstract) {
      std::vector<unsigned> children;
      for (const auto &child : binding.children) {
        auto selected = edge(context, child, depth + 1);
        if (!selected)
          return {};
        children.push_back(*selected);
      }
      auto contract =
          closedContract(binding.contract, context.statics, binding.span);
      return contract
                 ? residual(context, binding, *contract, std::move(children))
                 : std::nullopt;
    }
    const auto &definition = *callee.descriptorDefinition;
    Context nested{definition.bindings,
                   {},
                   {},
                   types.substitution(callee, arguments),
                   {},
                   {}};
    if (callee.parent &&
        declarations[callee.parent->index].kind == Declaration::Kind::Module) {
      const auto &module = declarations[callee.parent->index];
      Type self(Type::Kind::Module, module.qualifiedName);
      self.arguments.assign(arguments.begin(),
                            arguments.begin() + module.parameters.size());
      if (module.implementation)
        nested.statics.emplace("self:" + module.implementation->domain,
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
      auto selected = edge(context, binding.children[slot.index], depth + 1);
      if (!selected)
        return {};
      nested.domains[slot.index] = *selected;
    }
    auto expectedResult = callee.descriptorResult
                              ? closedContract(*callee.descriptorResult,
                                               nested.statics, binding.span)
                              : std::nullopt;
    auto actualResult =
        closedContract(binding.contract, context.statics, binding.span);
    if (!expectedResult || !actualResult || *expectedResult != *actualResult) {
      if (!types.diagnostic)
        refuse(binding.span, "selected factory result contract differs");
      return {};
    }
    for (unsigned i = 0; i < nested.domains.size(); ++i) {
      auto expected = closedContract(callee.descriptorInputs[i].contract,
                                     nested.statics, binding.span);
      if (!expected ||
          *expected != arena->payloads[nested.domains[i]].contract) {
        if (!types.diagnostic)
          refuse(binding.span, "selected factory child contract differs");
        return {};
      }
    }
    // Cache a selected recipe by its concrete static arguments and immutable
    // input places. Eager source operands have already run, and every domain
    // argument above has already joined this descriptor's admission graph.
    std::string key;
    auto append = [&](StringRef value) {
      return descriptorIdentityFrame(types, key, value, binding.span);
    };
    if (!append(std::to_string(target.index)))
      return {};
    for (const auto &argument : arguments) {
      if (!types.chargeIdentity(argument, binding.span))
        return {};
      frameTypeIdentity(key, argument);
    }
    if (!append("data"))
      return {};
    for (auto value : nested.data) {
      auto origin = origins.get(value, binding.span);
      if (!origin)
        return {};
      if (!append(std::to_string(origin->first)) ||
          !append(std::to_string(origin->second.size())))
        return {};
      for (auto field : origin->second)
        if (!append(std::to_string(field)))
          return {};
    }
    if (!append("domains"))
      return {};
    for (auto domain : nested.domains)
      if (!append(std::to_string(domain)))
        return {};
    uint64_t levels = 1;
    for (auto count = factories.size() + activeFactories.size(); count > 1;
         count >>= 1)
      ++levels;
    if (!types.charge((key.size() + 1) * levels * 3, binding.span))
      return {};
    if (activeFactories.count(key)) {
      refuse(binding.span, "cyclic selected descriptor admission");
      return {};
    }
    if (auto found = factories.find(key); found != factories.end()) {
      return occurrence(context, binding, found->second.first, nested.domains,
                        found->second.second)
                 ? std::optional(found->second.first)
                 : std::nullopt;
    }
    if (!activeFactories.insert(key).second) {
      refuse(binding.span, "cyclic selected domain factory");
      return {};
    }
    nested.block = arena->blocks.size();
    arena->blocks.emplace_back();
    // The complete selected recipe is the admission boundary, including nodes
    // not used to enumerate its result. All constructor edges remain explicit.
    for (const auto &[expression, selected] : definition.statements) {
      auto result = node(nested, selected, depth + 1);
      if (!result)
        return {};
      DescriptorBinding statement{DescriptorBinding::Kind::Parameter,
                                  arena->payloads[*result].contract,
                                  {},
                                  {},
                                  0,
                                  {},
                                  callee.span};
      statement.expression = expression;
      if (!occurrence(nested, statement, *result, {}))
        return {};
    }
    for (unsigned i = 0; i < nested.nodes.size(); ++i)
      if (!node(nested, i, depth + 1))
        return {};
    if (definition.result >= nested.nodes.size()) {
      refuse(binding.span, "factory result mapping differs");
      return {};
    }
    auto result = nested.memo.at(definition.result);
    activeFactories.erase(key);
    factories.emplace(std::move(key), std::make_pair(result, nested.block));
    return occurrence(context, binding, result, nested.domains, nested.block)
               ? std::optional(result)
               : std::nullopt;
  }
  std::optional<unsigned> edge(Context &context, const DescriptorEdge &child,
                               unsigned depth) {
    auto expected = closedContract(child.contract, context.statics, {});
    auto selected = expected ? node(context, child.node, depth) : std::nullopt;
    if (!selected || *expected != arena->payloads[*selected].contract) {
      if (!types.diagnostic)
        refuse({}, "descriptor child contract differs");
      return {};
    }
    return selected;
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
    if (binding.kind != DescriptorBinding::Kind::Parameter &&
        binding.parameter) {
      refuse(binding.span,
             "constructor has an unexpected descriptor parameter");
      return {};
    }
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
    if (binding.kind == DescriptorBinding::Kind::Parameter) {
      if (sourceJudgment && context.external) {
        auto contract =
            closedContract(binding.contract, context.statics, binding.span);
        if (!contract || !binding.parameter)
          return {};
        result = residual(context, binding, *contract, {}, binding.parameter);
        if (!result)
          return {};
        context.active.erase(index);
        context.memo.emplace(index, *result);
        return result;
      }
      if (!binding.parameter || *binding.parameter >= context.domains.size()) {
        refuse(binding.span, "unbound finite domain parameter");
        return {};
      }
      auto &selected = context.domains[*binding.parameter];
      if (context.external &&
          selected == std::numeric_limits<unsigned>::max()) {
        auto closed = embed(environment[*binding.parameter], binding, context);
        if (!closed)
          return {};
        selected = *closed;
      }
      result = selected;
    } else if (binding.kind == DescriptorBinding::Kind::Application)
      result = application(context, binding, depth);
    else {
      auto contract =
          closedContract(binding.contract, context.statics, binding.span);
      if (!contract)
        return {};
      if (!types.charge(sizeof(DescriptorPayload) +
                            binding.children.size() * sizeof(unsigned),
                        binding.span))
        return {};
      std::vector<unsigned> children;
      for (const auto &child : binding.children) {
        auto value = edge(context, child, depth + 1);
        if (!value)
          return {};
        children.push_back(*value);
      }
      using Kind = DescriptorBinding::Kind;
      // These source judgments retain their exact contract and source route.
      // Closure always re-evaluates them after actual inputs/statics are known.
      bool pending = false;
      if (sourceJudgment && binding.kind != Kind::StructuralProduct &&
          binding.kind != Kind::Sequence) {
        for (auto child : children)
          pending |= std::holds_alternative<DescriptorResidual>(
              arena->payloads[child].value);
        if (binding.kind == Kind::SequenceProjection ||
            binding.kind == Kind::Replace ||
            binding.kind == Kind::CheckExtent || binding.kind == Kind::Fold)
          for (const auto &argument : binding.arguments) {
            auto selected = type(argument, context.statics, binding.span);
            if (!selected)
              return {};
            pending |= types.symbolic(*selected);
          }
      }
      const auto payloadStart = arena->payloads.size();
      if (pending) {
        if (binding.kind == Kind::Fold) {
          std::set<unsigned> active;
          if (!binding.selectedView)
            return {};
          const auto &member = *binding.selectedView;
          std::vector<Type> arguments;
          for (const auto &argument : member.arguments) {
            auto selected = type(argument, context.statics, binding.span);
            if (!selected)
              return {};
            arguments.push_back(std::move(*selected));
          }
          // A generic interface route has no implementation body yet. Its
          // checked header supplies admission until actual dispatch at closure.
          if (!declarations[member.target.declaration.index].abstract &&
              !descriptorClosureAdmission(types, declarations,
                                          member.target.declaration, arguments,
                                          binding.span, active))
            return {};
        }
        result = residual(context, binding, *contract, std::move(children));
      } else if (binding.kind == Kind::ProductProjection ||
                 binding.kind == Kind::SequenceProjection) {
        if (children.size() != 1) {
          refuse(binding.span, "projection base coverage differs");
          return {};
        }
        const auto &base = arena->payloads[children.front()];
        if (binding.kind == Kind::ProductProjection) {
          auto *product = std::get_if<std::vector<unsigned>>(&base.value);
          if (!product || binding.axis >= product->size()) {
            types.fail("source.descriptor-projection",
                       "product component is out of range", binding.span);
            return {};
          }
          result = (*product)[binding.axis];
        } else {
          auto *sequence = std::get_if<uint64_t>(&base.value);
          auto index =
              binding.arguments.size() == 1
                  ? type(binding.arguments[0], context.statics, binding.span)
                  : std::nullopt;
          if (!sequence || !index || index->kind != Type::Kind::Natural ||
              !index->dimension.isClosed()) {
            refuse(binding.span, "sequence selector is not a closed Natural");
            return {};
          }
          result = sequences->at(*sequence, index->dimension.closedValue(),
                                 binding.span);
        }
      } else if (binding.kind == Kind::StructuralProduct) {
        result = arena->payloads.size();
        arena->payloads.push_back({*contract, children, {}});
      } else if (binding.kind == Kind::Sequence) {
        DescriptorSequence::Root root = DescriptorSequence::empty;
        for (auto child : children) {
          auto leaf = sequences->singleton(child, binding.span);
          auto next = leaf ? sequences->concat(root, *leaf, binding.span)
                           : std::nullopt;
          if (!next)
            return {};
          root = *next;
        }
        result = arena->payloads.size();
        arena->payloads.push_back({*contract, uint64_t(root), {}});
      } else if (binding.kind == Kind::Append || binding.kind == Kind::Concat ||
                 binding.kind == Kind::Replace ||
                 binding.kind == Kind::ForgetExtent ||
                 binding.kind == Kind::CheckExtent) {
        unsigned arity = binding.kind == Kind::ForgetExtent ||
                                 binding.kind == Kind::CheckExtent
                             ? 1
                             : 2;
        if (children.size() != arity) {
          refuse(binding.span, "structural scheme operand coverage differs");
          return {};
        }
        auto *base = std::get_if<uint64_t>(&arena->payloads[children[0]].value);
        if (!base) {
          refuse(binding.span, "structural scheme requires a sequence");
          return {};
        }
        std::optional<DescriptorSequence::Root> root = *base;
        if (binding.kind == Kind::Append) {
          auto tail = sequences->singleton(children[1], binding.span);
          root = tail ? sequences->concat(*root, *tail, binding.span)
                      : std::nullopt;
        } else if (binding.kind == Kind::Concat) {
          auto *tail =
              std::get_if<uint64_t>(&arena->payloads[children[1]].value);
          root = tail ? sequences->concat(*root, *tail, binding.span)
                      : std::nullopt;
        } else if (binding.kind == Kind::Replace ||
                   binding.kind == Kind::CheckExtent) {
          auto index =
              binding.arguments.size() == 1
                  ? type(binding.arguments[0], context.statics, binding.span)
                  : std::nullopt;
          if (!index || index->kind != Type::Kind::Natural ||
              !index->dimension.isClosed()) {
            refuse(binding.span,
                   "structural scheme static is not a closed Natural");
            return {};
          }
          auto value = index->dimension.closedValue();
          if (binding.kind == Kind::Replace)
            root = sequences->replace(*root, value, children[1], binding.span);
          else if (value != sequences->size(*root)) {
            types.fail("source.descriptor-contract",
                       "checked sequence extent differs", binding.span);
            return {};
          }
        }
        if (!root) {
          if (!types.diagnostic)
            refuse(binding.span, "structural sequence operands differ");
          return {};
        }
        result = arena->payloads.size();
        arena->payloads.push_back({*contract, uint64_t(*root), {}});
      } else if (binding.kind == Kind::Fold) {
        auto count =
            binding.arguments.size() == 1
                ? type(binding.arguments[0], context.statics, binding.span)
                : std::nullopt;
        auto route =
            descriptorSelection(types, declarations, binding, context.statics);
        if (!count || count->kind != Type::Kind::Natural ||
            !count->dimension.isClosed() || !route || children.size() != 2) {
          if (!types.diagnostic)
            refuse(binding.span, "Fold driver or selected operands differ");
          return {};
        }
        unsigned block = arena->blocks.size();
        arena->blocks.emplace_back();
        auto state = children[1];
        const auto &member = declarations[route->declaration.index];
        auto frame = descriptorFrameParameters(
            types, arena->payloads[children[0]].contract,
            arena->payloads[children[1]].contract, binding.span);
        if (!frame)
          return {};
        for (uint64_t i = 0; i < count->dimension.closedValue(); ++i) {
          if (!types.charge(1 + sizeof(Context), binding.span))
            return {};
          auto step =
              descriptorFrame(types, binding, context.statics,
                              (*frame)[0].contract, (*frame)[1].contract, i);
          if (!step)
            return {};
          Context iteration{*frame, {}, {children[0], state}, {}, {}, {}};
          iteration.block = block;
          auto next = application(iteration, *step, depth + 1);
          if (!next)
            return {};
          state = *next;
        }
        (void)member;
        result = state;
        if (!occurrence(context, binding, state, children, block))
          return {};
      } else {
        if (!finiteDescriptorItem(*contract)) {
          refuse(binding.span, "unsupported descriptor leaf boundary");
          return {};
        }
        DescriptorBinding closed{binding.kind, *contract, {},          {},
                                 binding.axis, {},        binding.span};
        for (auto operand : binding.operands) {
          if (operand.index >= context.data.size()) {
            refuse(binding.span, "domain operand mapping differs");
            return {};
          }
          auto value =
              input(context.data[operand.index], closed.contract, binding.span);
          if (!value)
            return {};
          closed.operands.push_back(*value);
        }
        for (auto child : children) {
          auto *leaf = std::get_if<unsigned>(&arena->payloads[child].value);
          if (!leaf) {
            refuse(binding.span, "Finite child is not a leaf");
            return {};
          }
          closed.children.push_back({*leaf, arena->payloads[child].contract});
        }
        unsigned constructorDepth = 1;
        for (auto child : closed.children)
          constructorDepth =
              std::max(constructorDepth, constructorDepths[child.node] + 1);
        if (arena->leaves.size() >= types.work.limits.operations) {
          types.fail("source.limit", "descriptor leaf operation bound exceeded",
                     binding.span);
          return {};
        }
        unsigned leaf = arena->leaves.size();
        constructorDepths.push_back(constructorDepth);
        arena->leaves.push_back(std::move(closed));
        result = arena->payloads.size();
        arena->payloads.push_back({*contract, leaf, {}});
      }
      if (sourceJudgment && result && !pending && binding.kind != Kind::Fold &&
          *result >= payloadStart && !finiteDescriptorItem(*contract)) {
        if (!types.charge(binding.arguments.size() * sizeof(Type),
                          binding.span))
          return {};
        for (const auto &argument : binding.arguments) {
          auto actual = type(argument, context.statics, binding.span);
          if (!actual)
            return {};
          arena->payloads[*result].arguments.push_back(std::move(*actual));
        }
      }
      if (result && !pending && binding.kind != Kind::Fold &&
          !occurrence(context, binding, *result, std::move(children)))
        return {};
    }
    if (!result)
      return {};
    auto expected =
        closedContract(binding.contract, context.statics, binding.span);
    if (!expected || *expected != arena->payloads[*result].contract) {
      if (!types.diagnostic)
        refuse(binding.span,
               "closed descriptor contract differs from its source");
      return {};
    }
    context.active.erase(index);
    context.memo.emplace(index, *result);
    return result;
  }

public:
  Closure(Semantics &types, ArrayRef<Declaration> declarations,
          const Body &body, const Substitution &statics,
          ArrayRef<DescriptorEnvironment> environment, ValueOrigins &origins,
          bool sourceJudgment = false)
      : types(types), declarations(declarations), body(body), statics(statics),
        environment(environment), origins(origins),
        sourceJudgment(sourceJudgment) {}
  std::optional<DescriptorEnvironment> run(unsigned root, bool all = false) {
    if (!types.charge(2 * body.values.size() * sizeof(ValueId) +
                          body.operations.size() +
                          environment.size() * sizeof(unsigned),
                      {}))
      return {};
    for (const auto &[key, value] : statics)
      if (!types.charge(key.size() + sizeof(Type) + 4 * sizeof(void *), {}) ||
          !types.chargeType(value, {}))
        return {};
    if (!types.charge(sizeof(DescriptorArena) + sizeof(DescriptorShape) +
                          4 * sizeof(void *),
                      {}))
      return {};
    arena = std::make_shared<DescriptorArena>();
    sequences.emplace(types, arena->sequences);
    arena->blocks.emplace_back();
    Context context{body.descriptorBindings, {}, {}, statics, {}, {}};
    for (unsigned i = 0; i < body.values.size(); ++i)
      context.data.push_back({i});
    context.domains.resize(environment.size(),
                           std::numeric_limits<unsigned>::max());
    context.external = true;
    if (all)
      for (unsigned i = 0; i < context.nodes.size(); ++i)
        if (!node(context, i, 1))
          return {};
    auto result = node(context, root, sourceJudgment ? 0 : 1);
    if (!result)
      return {};
    shape.payload = *result;
    shape.formation = context.block;
    shape.arena = arena;
    if (sourceJudgment)
      return DescriptorEnvironment{
          std::make_shared<DescriptorShape>(std::move(shape)),
          std::move(operands)};
    auto *leaf = std::get_if<unsigned>(&arena->payloads[*result].value);
    shape.result = UINT32_MAX;
    if (leaf) {
      if (!types.charge(arena->leaves.size() * sizeof(std::optional<unsigned>),
                        {}))
        return {};
      std::vector<std::optional<unsigned>> instances(arena->leaves.size());
      auto visit = [&](const DescriptorOccurrence &occurrence) {
        if (occurrence.invocation)
          return true;
        const auto &value = arena->payloads[occurrence.result];
        auto *selected = std::get_if<unsigned>(&value.value);
        // Projections and forwards reuse a payload; only its leaf-owned
        // constructor occurrence asserts admission.
        if (!selected ||
            occurrence.kind == DescriptorBinding::Kind::Parameter ||
            occurrence.kind == DescriptorBinding::Kind::ProductProjection ||
            occurrence.kind == DescriptorBinding::Kind::SequenceProjection)
          return true;
        if (*selected >= arena->leaves.size() || shape.nodes.size() >= maxNodes)
          return types.fail("source.limit",
                            "Finite projection exceeds constructor allowance",
                            {});
        const auto &source = arena->leaves[*selected];
        if (!chargeDescriptorBindingCopy(types, source))
          return false;
        auto copy = source;
        for (auto &child : copy.children) {
          if (child.node >= instances.size() || !instances[child.node])
            return refuse(source.span,
                          "Finite projection child has no activated formation");
          child.node = *instances[child.node];
        }
        if (!instances[*selected])
          instances[*selected] = shape.nodes.size();
        shape.nodes.push_back(std::move(copy));
        return true;
      };
      if (!FormationCursor(types, *arena).walk(shape.formation, visit) ||
          *leaf >= instances.size() || !instances[*leaf])
        return {};
      shape.result = *instances[*leaf];
    }
    if (leaf &&
        (shape.inputs.size() > maxInputs || shape.nodes.size() > maxNodes ||
         llvm::any_of(constructorDepths,
                      [](unsigned d) { return d > maxDepth; }))) {
      types.fail("source.limit", "finite descriptor constructor bound exceeded",
                 {});
      return {};
    }
    auto identityFrame = [&](StringRef value) {
      // Bound retained bytes and geometric string growth before appending.
      if (!types.diagnostic && types.charge(2 * (value.size() + 24), {}))
        frame(shape.identity, value);
    };
    identityFrame("descriptor");
    for (const auto &input : shape.inputs) {
      if (!types.chargeIdentity(input, {}))
        return {};
      frameTypeIdentity(shape.identity, input);
    }
    identityFrame("constructors");
    for (const auto &node : leaf ? shape.nodes : arena->leaves) {
      if (!types.chargeContract(node.contract, node.span) ||
          !types.chargeIdentity(descriptorType(node.contract), node.span) ||
          !types.charge(node.operands.size() + node.children.size() + 1,
                        node.span))
        return {};
      identityFrame(std::to_string(unsigned(node.kind)));
      frameTypeIdentity(shape.identity, descriptorType(node.contract));
      identityFrame(std::to_string(node.axis));
      identityFrame(std::to_string(node.operands.size()));
      for (auto operand : node.operands)
        identityFrame(std::to_string(operand.index));
      identityFrame(std::to_string(node.children.size()));
      for (const auto &child : node.children) {
        if (!types.chargeContract(child.contract, node.span) ||
            !types.chargeIdentity(descriptorType(child.contract), node.span))
          return {};
        identityFrame(std::to_string(child.node));
        frameTypeIdentity(shape.identity, descriptorType(child.contract));
      }
    }
    if (!leaf) {
      for (const auto &value : arena->payloads) {
        if (!types.chargeIdentity(descriptorType(value.contract), {}))
          return {};
        frameTypeIdentity(shape.identity, descriptorType(value.contract));
        identityFrame(std::to_string(value.value.index()));
        if (auto *leaf = std::get_if<unsigned>(&value.value))
          identityFrame(std::to_string(*leaf));
        else if (auto *product =
                     std::get_if<std::vector<unsigned>>(&value.value)) {
          identityFrame(std::to_string(product->size()));
          for (auto child : *product)
            identityFrame(std::to_string(child));
        } else
          identityFrame(std::to_string(std::get<uint64_t>(value.value)));
      }
      for (const auto &block : arena->blocks) {
        identityFrame("block");
        identityFrame(std::to_string(block.size()));
        for (const auto &event : block) {
          identityFrame(event.authority);
          identityFrame(std::to_string(unsigned(event.kind)));
          identityFrame(std::to_string(event.result));
          identityFrame(event.invocation ? std::to_string(*event.invocation)
                                         : "none");
          identityFrame(std::to_string(event.children.size()));
          for (auto child : event.children)
            identityFrame(std::to_string(child));
        }
      }
      for (const auto &node : arena->sequences) {
        identityFrame(std::to_string(node.length));
        identityFrame(std::to_string(node.count));
        identityFrame(std::to_string(node.height));
        identityFrame(std::to_string(node.left));
        identityFrame(std::to_string(node.right));
        for (unsigned i = 0; i < node.count; ++i)
          identityFrame(std::to_string(node.elements[i]));
      }
      identityFrame(std::to_string(shape.payload));
    }
    identityFrame(std::to_string(shape.result));
    if (types.diagnostic)
      return {};
    return DescriptorEnvironment{
        std::make_shared<DescriptorShape>(std::move(shape)),
        std::move(operands)};
  }
};
} // namespace
std::optional<DescriptorEnvironment>
closeDescriptor(Semantics &types, ArrayRef<Declaration> declarations,
                const Body &body, unsigned index, const Substitution &statics,
                ArrayRef<DescriptorEnvironment> environment,
                ValueOrigins *cache) {
  ValueOrigins localOrigins(types, body);
  auto &origins = cache ? *cache : localOrigins;
  if (!origins.describes(body)) {
    types.fail("source.finite-domain",
               "origin cache belongs to a different body", {});
    return {};
  }
  return Closure(types, declarations, body, statics, environment, origins)
      .run(index);
}
std::optional<DescriptorEnvironment>
formDescriptor(Semantics &types, ArrayRef<Declaration> declarations,
               const Body &body, unsigned index, const Substitution &statics,
               ValueOrigins *cache) {
  ValueOrigins local(types, body);
  auto &origins = cache ? *cache : local;
  if (!origins.describes(body)) {
    types.fail("source.descriptor", "formation origins belong to another Body",
               {});
    return {};
  }
  return Closure(types, declarations, body, statics, {}, origins, true)
      .run(index);
}
bool descriptorSourceAdmission(Semantics &types,
                               ArrayRef<Declaration> declarations,
                               DeclarationId target, ArrayRef<Type> arguments,
                               Span span) {
  const auto &member = declarations[target.index];
  if (!member.descriptorDefinition || !member.inputs.empty())
    return types.fail("source.view-selection",
                      "selected admission requires descriptor-only inputs",
                      span);
  const auto &definition = *member.descriptorDefinition;
  for (const auto &node : definition.bindings)
    if (!chargeDescriptorBindingCopy(types, node))
      return false;
  // This source judgment has no data values and invents no frame, iteration,
  // seed, or Body-local ValueId. Descriptor inputs remain typed residuals.
  Body source;
  source.descriptorBindings = definition.bindings;
  ValueOrigins origins(types, source);
  auto statics = descriptorSubstitution(types, member, arguments, span);
  if (!statics)
    return false;
  if (member.parent &&
      declarations[member.parent->index].kind == Declaration::Kind::Module) {
    const auto &owner = declarations[member.parent->index];
    if (owner.implementation) {
      if (!types.charge(owner.qualifiedName.size() +
                            owner.parameters.size() * sizeof(Type) +
                            sizeof(Substitution::value_type) +
                            4 * sizeof(void *) + 5 +
                            owner.implementation->domain.size(),
                        span))
        return false;
      Type self(Type::Kind::Module, owner.qualifiedName);
      self.arguments.reserve(owner.parameters.size());
      for (unsigned i = 0; i < owner.parameters.size(); ++i) {
        if (!types.chargeType(arguments[i], span))
          return false;
        self.arguments.push_back(arguments[i]);
      }
      statics->emplace("self:" + owner.implementation->domain, std::move(self));
    }
  }
  return Closure(types, declarations, source, *statics, {}, origins, true)
      .run(definition.result, true)
      .has_value();
}
} // namespace zkc::language::detail
