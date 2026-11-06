#include "DescriptorWitness.h"
#include "DescriptorFrames.h"
#include "DescriptorSequence.h"
#include "FormationCursor.h"
#include "ValueOrigins.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
namespace {
class DescriptorCheck {
  Semantics &types;
  ArrayRef<Declaration> declarations;
  const Body &body;
  const Substitution &statics;
  ArrayRef<DescriptorEnvironment> environment;
  const Body &caller;
  const std::function<ValueId(ValueId)> &map;
  const DescriptorShape &candidate;
  bool closedPayloads() {
    if (!candidate.arena)
      return refuse({}, "missing descriptor arena");
    for (const auto &payload : candidate.arena->payloads)
      if (!types.charge(1, {}) || !payload.arguments.empty() ||
          std::holds_alternative<DescriptorResidual>(payload.value))
        return types.diagnostic
                   ? false
                   : refuse({}, "source residual in closed descriptor");
    return true;
  }
  ValueOrigins &origins;
  std::vector<std::optional<ValueId>> ports;
  unsigned next = 0, nextPayload = 0, nextBlock = 1;
  std::map<unsigned, unsigned> eventPositions;
  std::vector<unsigned> depths;
  using Factory = std::tuple<unsigned, std::vector<std::string>,
                             std::vector<ValueOrigin>, std::vector<unsigned>>;
  /// Keyed by lookup keys; confined to this one witness pass.
  std::map<Factory, std::pair<unsigned, unsigned>> checkedFactories;
  std::set<Factory> activeFactories;
  struct Context {
    ArrayRef<DescriptorBinding> bindings;
    std::vector<ValueId> data;
    std::vector<unsigned> domains;
    Substitution statics;
    std::map<unsigned, unsigned> checked;
    std::set<unsigned> active;
    bool external = false;
    unsigned block = 0;
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
  std::optional<DescriptorContract>
  closedContract(const DescriptorContract &source,
                 const Substitution &substitution, Span span) {
    if (descriptorType(source).kind == Type::Kind::Descriptor &&
        !finiteDescriptorItem(source)) {
      refuse(span, "finite witness requires one item contract");
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
      refuse(span, "finite witness requires a Finite leaf contract");
      return {};
    }
    return contract;
  }
  bool bindPort(unsigned index, ValueId value,
                const DescriptorContract &contract, Span span) {
    if (index >= ports.size() || value.index >= caller.values.size())
      return refuse(span,
                    "descriptor operand mapping is outside its input space");
    auto actual = type(caller.values[value.index].type, statics, span);
    if (actual && descriptorType(contract).kind == Type::Kind::Descriptor) {
      auto permissions = types.permissions(*actual, span);
      if (!finiteDescriptorItem(contract) || !permissions ||
          !permissions->copy || !permissions->drop)
        return types.diagnostic
                   ? false
                   : refuse(span,
                            "finite operand permissions or contract differ");
    }
    if (!actual || *actual != candidate.inputs[index])
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
  std::optional<unsigned> constructor(const DescriptorBinding &source,
                                      const Substitution &substitution,
                                      ArrayRef<ValueId> data,
                                      ArrayRef<DescriptorEdge> children) {
    if (next >= candidate.arena->leaves.size()) {
      refuse(source.span, "descriptor omits an admitted constructor");
      return {};
    }
    const auto &actual = candidate.arena->leaves[next];
    if (!finiteDescriptorItem(actual.contract)) {
      refuse(source.span, "finite witness requires a Finite leaf contract");
      return {};
    }
    if (!types.chargeContract(actual.contract, source.span) ||
        !types.charge(actual.operands.size() + actual.children.size() + 1,
                      source.span))
      return {};
    for (const auto &child : actual.children)
      if (!finiteDescriptorItem(child.contract)) {
        refuse(source.span, "finite witness child requires a Finite leaf");
        return {};
      } else if (!types.chargeContract(child.contract, source.span))
        return {};
    auto contract = closedContract(source.contract, substitution, source.span);
    if (!contract || source.kind != actual.kind ||
        *contract != actual.contract || source.axis != actual.axis ||
        data.size() != actual.operands.size() ||
        children != ArrayRef(actual.children) || actual.factory ||
        actual.parameter || actual.expression || actual.selectedView ||
        !actual.arguments.empty() || !actual.argumentOrder.empty()) {
      if (!types.diagnostic)
        refuse(source.span, "admitted constructor differs from checked source");
      return {};
    }
    for (unsigned i = 0; i < data.size(); ++i)
      if (!bindPort(actual.operands[i].index, data[i], *contract, source.span))
        return {};
    unsigned depth = 1;
    for (auto child : children) {
      if (child.node >= next) {
        refuse(source.span, "constructor child does not precede its use");
        return {};
      }
      depth = std::max(depth, depths[child.node] + 1);
    }
    if (finiteDescriptorItem(
            candidate.arena->payloads[candidate.payload].contract) &&
        depth > 63) {
      types.fail("source.limit",
                 "descriptor constructor depth exceeds its bound", source.span);
      return {};
    }
    depths.push_back(depth);
    return next++;
  }
  bool event(Context &context, const DescriptorBinding &binding,
             unsigned result, ArrayRef<unsigned> children,
             std::optional<unsigned> invocation = {}) {
    if (context.block >= candidate.arena->blocks.size())
      return refuse(binding.span, "missing source invocation block");
    const auto &block = candidate.arena->blocks[context.block];
    auto &position = eventPositions[context.block];
    if (position >= block.size())
      return refuse(binding.span, "missing ordered formation occurrence");
    const auto &actual = block[position++];
    auto authority =
        descriptorOccurrenceAuthority(types, binding, context.statics);
    if (!authority)
      return false;
    return (actual.authority == *authority && actual.kind == binding.kind &&
            actual.expression == binding.expression &&
            actual.result == result && ArrayRef(actual.children) == children &&
            actual.invocation == invocation) ||
           refuse(binding.span, "ordered source formation occurrence differs");
  }
  std::optional<unsigned> payload(const DescriptorContract &contract,
                                  Span span) {
    if (nextPayload >= candidate.arena->payloads.size() ||
        !types.charge(sizeof(DescriptorPayload), span)) {
      if (!types.diagnostic)
        refuse(span, "descriptor omits a source payload");
      return {};
    }
    const auto &actual = candidate.arena->payloads[nextPayload];
    if (!types.chargeContract(actual.contract, span) ||
        actual.contract != contract) {
      if (!types.diagnostic)
        refuse(span, "descriptor payload contract differs");
      return {};
    }
    return nextPayload++;
  }
  uint64_t sequenceLength(uint64_t root) const {
    return root == UINT32_MAX ? 0 : candidate.arena->sequences[root].length;
  }
  bool sequenceStorage() {
    return checkClosedDescriptorStorage(types, candidate, {},
                                        "source.domain-witness");
  }
  std::optional<unsigned> sequenceAt(uint64_t root, uint64_t index, Span span) {
    const auto &nodes = candidate.arena->sequences;
    if ((root != UINT32_MAX && root >= nodes.size()) ||
        index >= sequenceLength(root)) {
      refuse(span, "sequence index is outside its payload");
      return {};
    }
    while (true) {
      if (!types.charge(1, span))
        return {};
      const auto &node = nodes[root];
      if (node.count)
        return node.elements[index];
      auto left = nodes[node.left].length;
      if (index < left)
        root = node.left;
      else {
        index -= left;
        root = node.right;
      }
    }
  }
  bool sequenceRange(uint64_t a, uint64_t beginA, uint64_t b, uint64_t beginB,
                     uint64_t length, Span span) {
    const auto &nodes = candidate.arena->sequences;
    if ((a != UINT32_MAX && a >= nodes.size()) ||
        (b != UINT32_MAX && b >= nodes.size()) || beginA > sequenceLength(a) ||
        length > sequenceLength(a) - beginA || beginB > sequenceLength(b) ||
        length > sequenceLength(b) - beginB)
      return refuse(span, "sequence relation range differs");
    struct Pair {
      uint64_t a, beginA, b, beginB, length;
    };
    std::vector<Pair> pending;
    if (length)
      pending.push_back({a, beginA, b, beginB, length});
    while (!pending.empty()) {
      if (!types.charge(sizeof(Pair), span))
        return false;
      auto pair = pending.back();
      pending.pop_back();
      auto normalize = [&](uint64_t &root, uint64_t &begin) {
        while (!nodes[root].count) {
          if (!types.charge(1, span))
            return false;
          auto left = nodes[nodes[root].left].length;
          if (begin >= left) {
            begin -= left;
            root = nodes[root].right;
          } else if (pair.length <= left - begin)
            root = nodes[root].left;
          else
            break;
        }
        return true;
      };
      if (!normalize(pair.a, pair.beginA) || !normalize(pair.b, pair.beginB))
        return false;
      if (pair.a == pair.b && pair.beginA == pair.beginB)
        continue;
      const auto &left = nodes[pair.a], &right = nodes[pair.b];
      if (left.count && right.count) {
        if (!types.charge(pair.length, span))
          return false;
        for (uint64_t i = 0; i < pair.length; ++i)
          if (left.elements[pair.beginA + i] != right.elements[pair.beginB + i])
            return refuse(span, "ordered sequence payload relation differs");
        continue;
      }
      auto boundaryA =
          left.count ? pair.length : nodes[left.left].length - pair.beginA;
      auto boundaryB =
          right.count ? pair.length : nodes[right.left].length - pair.beginB;
      auto split = std::min(boundaryA, boundaryB);
      if (!split || split >= pair.length)
        return refuse(span, "invalid sequence relation split");
      pending.push_back({pair.a, pair.beginA + split, pair.b,
                         pair.beginB + split, pair.length - split});
      pending.push_back({pair.a, pair.beginA, pair.b, pair.beginB, split});
    }
    return true;
  }
  std::optional<std::vector<unsigned>> sequence(uint64_t root, Span span) {
    const auto &nodes = candidate.arena->sequences;
    if (root == UINT32_MAX)
      return std::vector<unsigned>{};
    if (root >= nodes.size()) {
      refuse(span, "foreign sequence root");
      return {};
    }
    std::vector<unsigned> result;
    std::vector<uint32_t> pending{uint32_t(root)};
    while (!pending.empty()) {
      auto index = pending.back();
      pending.pop_back();
      if (!types.charge(sizeof(unsigned) + 1, span))
        return {};
      const auto &node = nodes[index];
      if (node.count) {
        if (node.count > node.elements.size() || node.length != node.count ||
            node.height != 1 || node.left != UINT32_MAX ||
            node.right != UINT32_MAX) {
          refuse(span, "malformed immutable sequence chunk");
          return {};
        }
        if (!types.charge(node.count * sizeof(unsigned), span))
          return {};
        for (unsigned i = 0; i < node.count; ++i)
          result.push_back(node.elements[i]);
      } else {
        if (node.left >= index || node.right >= index) {
          refuse(span, "sequence branch is cyclic or not topological");
          return {};
        }
        const auto &a = nodes[node.left], &b = nodes[node.right];
        if (a.length > UINT64_MAX - b.length ||
            node.length != a.length + b.length ||
            node.height != std::max(a.height, b.height) + 1 ||
            a.height > b.height + 1 || b.height > a.height + 1) {
          refuse(span, "sequence branch length or AVL invariant differs");
          return {};
        }
        pending.push_back(node.right);
        pending.push_back(node.left);
      }
    }
    return result;
  }
  std::optional<unsigned> inherited(const DescriptorEnvironment &expected,
                                    const DescriptorBinding &parameter,
                                    Context &parent) {
    if (!expected.shape || !expected.shape->arena ||
        expected.operands.size() != expected.shape->inputs.size() ||
        expected.shape->payload >= expected.shape->arena->payloads.size()) {
      refuse(parameter.span, "invalid inherited descriptor witness");
      return {};
    }
    const auto &source = *expected.shape;
    const auto &storage = *source.arena;
    if (!checkClosedDescriptorStorage(types, source, parameter.span,
                                      "source.domain-witness"))
      return {};
    unsigned leafBase = next, payloadBase = nextPayload, blockBase = nextBlock;
    // The expected universe belongs to the already admitted immutable source
    // environment. Inspect its relations directly; never invoke its producer.
    for (const auto &leaf : storage.leaves) {
      std::vector<ValueId> data;
      for (auto value : leaf.operands) {
        if (value.index >= expected.operands.size()) {
          refuse(parameter.span, "inherited source operand differs");
          return {};
        }
        data.push_back(expected.operands[value.index]);
      }
      auto children = leaf.children;
      for (auto &child : children)
        child.node += leafBase;
      if (!constructor(leaf, {}, data, children))
        return {};
    }
    std::optional<uint64_t> sequenceBase;
    auto sequenceCopy = [&](uint64_t sourceRoot, uint64_t actualRoot) {
      if (sourceRoot == UINT32_MAX)
        return actualRoot == UINT32_MAX ||
               refuse(parameter.span, "inherited empty sequence differs");
      if (sourceRoot >= storage.sequences.size() || actualRoot < sourceRoot ||
          actualRoot >= candidate.arena->sequences.size())
        return refuse(parameter.span, "inherited sequence root differs");
      auto offset = actualRoot - sourceRoot;
      if (sequenceBase)
        return offset == *sequenceBase ||
               refuse(parameter.span, "inherited sequence offset differs");
      if (offset > candidate.arena->sequences.size() ||
          storage.sequences.size() > candidate.arena->sequences.size() - offset)
        return refuse(parameter.span, "inherited sequence storage is missing");
      sequenceBase = offset;
      // Compare each immutable cell once, including retained historical roots.
      // No flattening of every prior persistent sequence is necessary.
      for (unsigned i = 0; i < storage.sequences.size(); ++i) {
        const auto &a = storage.sequences[i];
        const auto &b = candidate.arena->sequences[offset + i];
        if (!types.charge(sizeof(DescriptorSequenceNode), parameter.span))
          return false;
        if (a.length != b.length || a.height != b.height ||
            a.count != b.count || a.count > a.elements.size())
          return refuse(parameter.span, "inherited sequence cell differs");
        if (a.count) {
          if (a.left != UINT32_MAX || a.right != UINT32_MAX ||
              b.left != UINT32_MAX || b.right != UINT32_MAX)
            return refuse(parameter.span, "inherited sequence chunk differs");
          for (unsigned j = 0; j < a.count; ++j)
            if (a.elements[j] >= storage.payloads.size() ||
                b.elements[j] != a.elements[j] + payloadBase)
              return refuse(parameter.span,
                            "inherited sequence element differs");
        } else if (a.left >= i || a.right >= i || b.left != a.left + offset ||
                   b.right != a.right + offset)
          return refuse(parameter.span, "inherited sequence branch differs");
      }
      return true;
    };
    for (const auto &value : storage.payloads) {
      auto index = payload(value.contract, parameter.span);
      if (!index)
        return {};
      const auto &actual = candidate.arena->payloads[*index];
      if (auto *leaf = std::get_if<unsigned>(&value.value)) {
        auto *mapped = std::get_if<unsigned>(&actual.value);
        if (!mapped || *mapped != leafBase + *leaf) {
          refuse(parameter.span, "inherited leaf relation differs");
          return {};
        }
      } else if (auto *product =
                     std::get_if<std::vector<unsigned>>(&value.value)) {
        auto *mapped = std::get_if<std::vector<unsigned>>(&actual.value);
        if (!mapped || mapped->size() != product->size()) {
          refuse(parameter.span, "inherited product relation differs");
          return {};
        }
        for (unsigned i = 0; i < product->size(); ++i)
          if ((*mapped)[i] != (*product)[i] + payloadBase) {
            refuse(parameter.span, "inherited product edge differs");
            return {};
          }
      } else {
        auto *root = std::get_if<uint64_t>(&value.value);
        auto *mapped = std::get_if<uint64_t>(&actual.value);
        if (!root || !mapped || !sequenceCopy(*root, *mapped))
          return types.diagnostic
                     ? std::nullopt
                     : (refuse(parameter.span,
                               "inherited sequence relation differs"),
                        std::nullopt);
      }
    }
    for (const auto &sourceBlock : storage.blocks) {
      unsigned block = nextBlock++;
      if (block >= candidate.arena->blocks.size() ||
          candidate.arena->blocks[block].size() != sourceBlock.size()) {
        refuse(parameter.span, "inherited invocation coverage differs");
        return {};
      }
      for (unsigned i = 0; i < sourceBlock.size(); ++i) {
        if (!types.charge(sourceBlock[i].children.size() + 1, parameter.span))
          return {};
        const auto &a = sourceBlock[i], &b = candidate.arena->blocks[block][i];
        if (a.authority != b.authority || a.kind != b.kind ||
            a.expression != b.expression ||
            a.result + payloadBase != b.result ||
            a.children.size() != b.children.size() ||
            (a.invocation ? std::optional(*a.invocation + blockBase)
                          : std::nullopt) != b.invocation) {
          refuse(parameter.span, "inherited formation occurrence differs");
          return {};
        }
        for (unsigned j = 0; j < a.children.size(); ++j)
          if (a.children[j] + payloadBase != b.children[j]) {
            refuse(parameter.span, "inherited formation input differs");
            return {};
          }
      }
      eventPositions[block] = sourceBlock.size();
    }
    unsigned result = payloadBase + source.payload;
    if (!event(parent, parameter, result, {}, blockBase + source.formation))
      return {};
    return result;
  }
  std::optional<unsigned> application(Context &context,
                                      const DescriptorBinding &binding,
                                      unsigned depth) {
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
      arguments.push_back(std::move(*value));
    }
    if (binding.factory->module) {
      auto module =
          type(*binding.factory->module, context.statics, binding.span);
      if (!module)
        return {};
      auto selected = types.dispatch(*module, target, arguments, binding.span);
      if (!selected)
        return {};
      target = selected->declaration;
      arguments = std::move(selected->arguments);
    }
    const auto &callee = declarations[target.index];
    if (callee.kind != Declaration::Kind::View || callee.abstract ||
        !callee.descriptorDefinition ||
        binding.operands.size() != callee.inputs.size() ||
        binding.children.size() != callee.descriptorInputs.size() ||
        !types.checkArguments(callee, arguments, binding.span)) {
      if (!types.diagnostic)
        refuse(binding.span, "factory has no checked concrete definition");
      return {};
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
      if (!types.chargeIdentity(argument, binding.span))
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
        auto selected = edge(context, binding.children[slot.index], depth + 1);
        if (!selected)
          return {};
        nested.domains[slot.index] = *selected;
      }
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
          *expected != candidate.arena->payloads[nested.domains[i]].contract) {
        if (!types.diagnostic)
          refuse(binding.span, "selected factory child contract differs");
        return {};
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
    if (activeFactories.count(identity)) {
      refuse(binding.span, "cyclic selected descriptor admission");
      return {};
    }
    if (auto found = checkedFactories.find(identity);
        found != checkedFactories.end()) {
      if (!event(context, binding, found->second.first, nested.domains,
                 found->second.second))
        return {};
      return found->second.first;
    }
    if (!activeFactories.insert(identity).second) {
      refuse(binding.span, "cyclic source factory selection");
      return {};
    }
    nested.block = nextBlock++;
    for (const auto &[expression, selected] : definition.statements) {
      auto result = node(nested, selected, depth + 1);
      if (!result)
        return {};
      DescriptorBinding statement{DescriptorBinding::Kind::Parameter,
                                  candidate.arena->payloads[*result].contract,
                                  {},
                                  {},
                                  0,
                                  {},
                                  callee.span};
      statement.expression = expression;
      if (!event(nested, statement, *result, {}))
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
    if (!event(context, binding, result, nested.domains, nested.block))
      return {};
    checkedFactories.emplace(std::move(identity),
                             std::make_pair(result, nested.block));
    return result;
  }
  std::optional<unsigned> edge(Context &context, const DescriptorEdge &child,
                               unsigned depth) {
    auto expected = closedContract(child.contract, context.statics, {});
    auto selected = expected ? node(context, child.node, depth) : std::nullopt;
    if (!selected ||
        *expected != candidate.arena->payloads[*selected].contract) {
      if (!types.diagnostic)
        refuse({}, "descriptor child contract differs");
      return {};
    }
    return selected;
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
    if (binding.kind == DescriptorBinding::Kind::Parameter) {
      if (!binding.parameter || *binding.parameter >= context.domains.size()) {
        refuse(binding.span, "unbound domain parameter in witness");
        return {};
      }
      auto &selected = context.domains[*binding.parameter];
      if (context.external &&
          selected == std::numeric_limits<unsigned>::max()) {
        auto actual =
            inherited(environment[*binding.parameter], binding, context);
        if (!actual)
          return {};
        selected = *actual;
      }
      result = selected;
    } else if (binding.kind == DescriptorBinding::Kind::Application)
      result = application(context, binding, depth);
    else {
      std::vector<unsigned> children;
      for (const auto &child : binding.children) {
        auto selected = edge(context, child, depth + 1);
        if (!selected)
          return {};
        children.push_back(*selected);
      }
      auto contract =
          closedContract(binding.contract, context.statics, binding.span);
      if (!contract)
        return {};
      using Kind = DescriptorBinding::Kind;
      if (binding.kind == Kind::ProductProjection ||
          binding.kind == Kind::SequenceProjection) {
        if (children.size() != 1) {
          refuse(binding.span, "projection base coverage differs");
          return {};
        }
        const auto &base = candidate.arena->payloads[children.front()];
        if (binding.kind == Kind::ProductProjection) {
          auto *edges = std::get_if<std::vector<unsigned>>(&base.value);
          if (!edges || binding.axis >= edges->size()) {
            refuse(binding.span, "product projection differs");
            return {};
          }
          result = (*edges)[binding.axis];
        } else {
          auto *root = std::get_if<uint64_t>(&base.value);
          auto index =
              binding.arguments.size() == 1
                  ? type(binding.arguments[0], context.statics, binding.span)
                  : std::nullopt;
          if (!root || !index || index->kind != Type::Kind::Natural ||
              !index->dimension.isClosed()) {
            if (!types.diagnostic)
              refuse(binding.span, "sequence projection differs");
            return {};
          }
          result =
              sequenceAt(*root, index->dimension.closedValue(), binding.span);
          if (!result)
            return {};
        }
      } else if (binding.kind == Kind::StructuralProduct ||
                 binding.kind == Kind::Sequence) {
        result = payload(*contract, binding.span);
        if (!result)
          return {};
        const auto &actual = candidate.arena->payloads[*result];
        if (binding.kind == Kind::StructuralProduct) {
          auto *edges = std::get_if<std::vector<unsigned>>(&actual.value);
          if (!edges || *edges != children) {
            refuse(binding.span, "ordered structural product edges differ");
            return {};
          }
        } else {
          auto *root = std::get_if<uint64_t>(&actual.value);
          auto values = root ? sequence(*root, binding.span) : std::nullopt;
          if (!values || *values != children) {
            if (!types.diagnostic)
              refuse(binding.span, "ordered sequence payload differs");
            return {};
          }
        }
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
        auto *base = std::get_if<uint64_t>(
            &candidate.arena->payloads[children[0]].value);
        result = payload(*contract, binding.span);
        if (!base || !result)
          return {};
        auto *root =
            std::get_if<uint64_t>(&candidate.arena->payloads[*result].value);
        if (!root ||
            (*base != UINT32_MAX &&
             *base >= candidate.arena->sequences.size()) ||
            (*root != UINT32_MAX &&
             *root >= candidate.arena->sequences.size())) {
          refuse(binding.span, "structural scheme has a foreign sequence root");
          return {};
        }
        auto length = sequenceLength(*base),
             actualLength = sequenceLength(*root);
        if (binding.kind == Kind::Append) {
          if (length == UINT64_MAX || actualLength != length + 1 ||
              !sequenceRange(*base, 0, *root, 0, length, binding.span) ||
              sequenceAt(*root, length, binding.span) != children[1]) {
            if (!types.diagnostic)
              refuse(binding.span, "Append sequence relation differs");
            return {};
          }
        } else if (binding.kind == Kind::Concat) {
          auto *tail = std::get_if<uint64_t>(
              &candidate.arena->payloads[children[1]].value);
          if (!tail ||
              (*tail != UINT32_MAX &&
               *tail >= candidate.arena->sequences.size()) ||
              length > UINT64_MAX - sequenceLength(*tail) ||
              actualLength != length + sequenceLength(*tail) ||
              !sequenceRange(*base, 0, *root, 0, length, binding.span) ||
              !sequenceRange(*tail, 0, *root, length, sequenceLength(*tail),
                             binding.span)) {
            if (!types.diagnostic)
              refuse(binding.span, "Concat sequence relation differs");
            return {};
          }
        } else {
          if (actualLength != length) {
            refuse(binding.span, "structural scheme changes sequence length");
            return {};
          }
          uint64_t index = 0;
          if (binding.kind != Kind::ForgetExtent) {
            auto value =
                binding.arguments.size() == 1
                    ? type(binding.arguments[0], context.statics, binding.span)
                    : std::nullopt;
            if (!value || value->kind != Type::Kind::Natural ||
                !value->dimension.isClosed()) {
              refuse(binding.span, "structural static is not a closed Natural");
              return {};
            }
            index = value->dimension.closedValue();
          }
          if (binding.kind == Kind::Replace) {
            if (index >= length ||
                sequenceAt(*root, index, binding.span) != children[1] ||
                !sequenceRange(*base, 0, *root, 0, index, binding.span) ||
                !sequenceRange(*base, index + 1, *root, index + 1,
                               length - index - 1, binding.span)) {
              if (!types.diagnostic)
                refuse(binding.span, "Replace sequence relation differs");
              return {};
            }
          } else if ((binding.kind == Kind::CheckExtent && index != length) ||
                     !sequenceRange(*base, 0, *root, 0, length, binding.span)) {
            if (!types.diagnostic)
              refuse(binding.span,
                     "extent contract or sequence relation differs");
            return {};
          }
        }
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
        unsigned block = nextBlock++;
        auto state = children[1];
        auto frame = descriptorFrameParameters(
            types, candidate.arena->payloads[children[0]].contract,
            candidate.arena->payloads[children[1]].contract, binding.span);
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
        result = state;
        if (!event(context, binding, state, children, block))
          return {};
      } else {
        std::vector<ValueId> data;
        std::vector<DescriptorEdge> edges;
        for (auto operand : binding.operands) {
          if (operand.index >= context.data.size()) {
            refuse(binding.span, "constructor data edge differs");
            return {};
          }
          data.push_back(context.data[operand.index]);
        }
        for (auto child : children) {
          const auto &value = candidate.arena->payloads[child];
          auto *leaf = std::get_if<unsigned>(&value.value);
          if (!leaf) {
            refuse(binding.span, "Finite child is not a leaf");
            return {};
          }
          edges.push_back({*leaf, value.contract});
        }
        auto leaf = constructor(binding, context.statics, data, edges);
        result = leaf ? payload(*contract, binding.span) : std::nullopt;
        if (!result)
          return {};
        auto *actual =
            std::get_if<unsigned>(&candidate.arena->payloads[*result].value);
        if (!actual || *actual != *leaf) {
          refuse(binding.span, "Finite payload-to-formation relation differs");
          return {};
        }
      }
      if (!result || (binding.kind != Kind::Fold &&
                      !event(context, binding, *result, children)))
        return {};
    }
    if (!result)
      return {};
    auto expected =
        closedContract(binding.contract, context.statics, binding.span);
    if (!expected || *expected != candidate.arena->payloads[*result].contract) {
      if (!types.diagnostic)
        refuse(binding.span, "descriptor result contract differs");
      return {};
    }
    context.active.erase(index);
    context.checked.emplace(index, *result);
    return result;
  }

public:
  DescriptorCheck(Semantics &types, ArrayRef<Declaration> declarations,
                  const Body &body, const Body &caller,
                  const std::function<ValueId(ValueId)> &map,
                  const Substitution &statics,
                  ArrayRef<DescriptorEnvironment> environment,
                  const DescriptorShape &candidate, ValueOrigins &origins)
      : types(types), declarations(declarations), body(body), statics(statics),
        environment(environment), caller(caller), map(map),
        candidate(candidate), origins(origins) {}
  bool run(unsigned root) {
    if (!candidate.arena ||
        candidate.payload >= candidate.arena->payloads.size() ||
        candidate.formation != 0 || candidate.arena->blocks.empty())
      return refuse({}, "invalid descriptor witness shape");
    if (!closedPayloads())
      return false;
    if (finiteDescriptorItem(
            candidate.arena->payloads[candidate.payload].contract) &&
        (candidate.inputs.size() > 1024 ||
         candidate.arena->leaves.size() > 4095))
      return types.fail("source.limit",
                        "descriptor witness exceeds formation bounds", {});
    if (!types.charge(2 * body.values.size() * sizeof(ValueId) +
                          candidate.inputs.size() *
                              sizeof(std::optional<ValueId>) +
                          environment.size() * sizeof(unsigned) +
                          candidate.arena->leaves.size() + 1,
                      {}))
      return false;
    for (const auto &[key, value] : statics)
      if (!types.charge(key.size() + sizeof(Type) + 4 * sizeof(void *), {}) ||
          !types.chargeType(value, {}))
        return false;
    for (const auto &input : candidate.inputs)
      if (!types.chargeType(input, {}))
        return false;
    if (!sequenceStorage())
      return false;
    ports.resize(candidate.inputs.size());
    Context context{body.descriptorBindings, {}, {}, statics, {}, {}};
    for (unsigned i = 0; i < body.values.size(); ++i)
      context.data.push_back(map({i}));
    context.domains.resize(environment.size(),
                           std::numeric_limits<unsigned>::max());
    context.external = true;
    auto selected = node(context, root, 1);
    if (!selected || *selected != candidate.payload ||
        next != candidate.arena->leaves.size() ||
        nextPayload != candidate.arena->payloads.size() ||
        nextBlock != candidate.arena->blocks.size())
      return types.diagnostic
                 ? false
                 : refuse({},
                          "descriptor admission or result coverage differs");
    for (unsigned i = 0; i < candidate.arena->blocks.size(); ++i)
      if (eventPositions[i] != candidate.arena->blocks[i].size())
        return refuse({}, "formation block has unauthored occurrences");
    const auto *leaf =
        std::get_if<unsigned>(&candidate.arena->payloads[*selected].value);
    unsigned projected = 0;
    std::vector<std::optional<unsigned>> instances(
        candidate.arena->leaves.size());
    if (leaf) {
      auto visit = [&](const DescriptorOccurrence &occurrence) {
        if (occurrence.invocation)
          return true;
        const auto &value = candidate.arena->payloads[occurrence.result];
        auto *selected = std::get_if<unsigned>(&value.value);
        if (!selected ||
            occurrence.kind == DescriptorBinding::Kind::Parameter ||
            occurrence.kind == DescriptorBinding::Kind::ProductProjection ||
            occurrence.kind == DescriptorBinding::Kind::SequenceProjection)
          return true;
        if (*selected >= candidate.arena->leaves.size() ||
            projected >= candidate.nodes.size() || projected >= 4095)
          return refuse({}, "Finite projection coverage differs");
        const auto &source = candidate.arena->leaves[*selected],
                   &actual = candidate.nodes[projected];
        if (!types.charge(source.children.size() + source.operands.size() + 1,
                          source.span) ||
            source.kind != actual.kind || source.contract != actual.contract ||
            source.axis != actual.axis ||
            !llvm::equal(
                source.operands, actual.operands,
                [](ValueId a, ValueId b) { return a.index == b.index; }) ||
            source.children.size() != actual.children.size() ||
            actual.parameter || actual.factory || actual.expression ||
            !actual.arguments.empty() || !actual.argumentOrder.empty() ||
            actual.selectedView)
          return types.diagnostic
                     ? false
                     : refuse(source.span, "Finite projection leaf differs");
        for (unsigned i = 0; i < source.children.size(); ++i) {
          const auto &edge = source.children[i], &provided = actual.children[i];
          if (edge.node >= instances.size() || !instances[edge.node] ||
              *instances[edge.node] != provided.node ||
              edge.contract != provided.contract)
            return refuse(source.span,
                          "Finite projection child relation differs");
        }
        if (!instances[*selected])
          instances[*selected] = projected;
        ++projected;
        return true;
      };
      if (!FormationCursor(types, *candidate.arena)
               .walk(candidate.formation, visit))
        return false;
    }
    if (projected != candidate.nodes.size() ||
        candidate.result !=
            (leaf && *leaf < instances.size() && instances[*leaf]
                 ? *instances[*leaf]
                 : UINT32_MAX))
      return refuse({}, "selected Finite result or all-node coverage differs");
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
bindDescriptorInputs(Semantics &types, ArrayRef<Declaration> declarations,
                     const Body &source, const Body &caller,
                     const std::function<ValueId(ValueId)> &map, unsigned root,
                     const Substitution &statics,
                     ArrayRef<DescriptorEnvironment> environment,
                     const DescriptorShape &candidate, ValueOrigins *cache) {
  ValueOrigins localOrigins(types, caller);
  auto &origins = cache ? *cache : localOrigins;
  if (!origins.describes(caller)) {
    types.fail("source.domain-witness",
               "origin cache belongs to a different body", {});
    return {};
  }
  DescriptorCheck check(types, declarations, source, caller, map, statics,
                        environment, candidate, origins);
  if (!check.run(root))
    return {};
  return check.inputs();
}
bool checkDescriptorClosure(Semantics &types,
                            ArrayRef<Declaration> declarations,
                            const Body &body, unsigned root,
                            const Substitution &statics,
                            ArrayRef<DescriptorEnvironment> environment,
                            const DescriptorEnvironment &candidate,
                            ValueOrigins *cache) {
  if (!candidate.shape ||
      candidate.operands.size() != candidate.shape->inputs.size())
    return types.fail("source.domain-witness",
                      "invalid descriptor operand coverage", {});
  ValueOrigins localOrigins(types, body);
  auto &origins = cache ? *cache : localOrigins;
  auto inputs = bindDescriptorInputs(
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
