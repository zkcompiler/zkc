#include "zkc/Analysis/CommonControl.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Interfaces/Collection.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringMap.h"
#include <set>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
using Term = unsigned;
using Components = SmallVector<Term>;
using Environment = llvm::DenseMap<Value, Components>;
struct Node {
  enum Kind { Expression, Input, Carry, Exit, Iteration } kind = Expression;
  Type type;
  StringAttr name;
  DictionaryAttr attributes;
  unsigned coordinate = 0;
  unsigned alternative = 0;
  Components operands;
  CommonControlComponent input;
  bool tagOnly = false;
  std::optional<unsigned> extentAxis;
  bool complete = true;
  // Symbolic nodes belong to an actual traversal of a loop, not its printed
  // attributes. Keep each role distinct until its equation has been checked.
  unsigned invocation = 0;
  unsigned role = 0;
  SmallVector<Type> projectionTypes;
};
struct Recurrence {
  Components count;
  SmallVector<Components> initial, transition;
  bool atMostOne = false;
};
struct Demand {
  Term left, right;
  Operation *control;
};
struct Derivation {
  pir::MathematicalOp entry;
  facts::Work &work;
  SymbolTableCollection symbols;
  SmallVector<Node, 0> nodes{Node{}};
  SmallVector<Recurrence> recurrences;
  SmallVector<Demand> demands;
  SmallVector<CommonControlRequirement> requirements;
  llvm::DenseSet<Operation *> active;
  unsigned roles;
  unsigned observationDepth = 0;
  Derivation(pir::MathematicalOp entry, facts::Work &work)
      : entry(entry), work(work), roles(entry.getRoles().size()) {}

  Error failure() {
    return error(work.exhausted() ? "common-control-capacity"
                                  : "common-control-provenance");
  }
  bool charge(uint64_t amount = 1) { return work.charge(amount); }
  Components absent() const { return Components(roles, 0); }
  Term intern(Node node) {
    if (!charge(1 + node.operands.size() + node.input.path.size() +
                node.projectionTypes.size()))
      return 0;
    for (unsigned i = 1; i < nodes.size(); ++i) {
      if (!charge(1 + nodes[i].operands.size() + nodes[i].input.path.size() +
                  nodes[i].projectionTypes.size()))
        return 0;
      const auto &old = nodes[i];
      if (old.kind == node.kind && old.type == node.type &&
          old.name == node.name && old.attributes == node.attributes &&
          old.coordinate == node.coordinate && old.operands == node.operands &&
          old.alternative == node.alternative &&
          old.input.input == node.input.input &&
          old.input.role == node.input.role &&
          old.input.path == node.input.path && old.tagOnly == node.tagOnly &&
          old.extentAxis == node.extentAxis &&
          old.invocation == node.invocation && old.role == node.role &&
          old.projectionTypes == node.projectionTypes)
        return i;
    }
    nodes.push_back(std::move(node));
    return nodes.size() - 1;
  }
  Term expression(StringRef name, Type type, DictionaryAttr attributes,
                  ArrayRef<Term> inputs, unsigned coordinate = 0) {
    bool complete = all_of(
        inputs, [&](Term input) { return input && nodes[input].complete; });
    // A constructor's tag remains static even when a payload has ordered
    // provenance. Its full value is still unavailable for congruence.
    if (!complete && name != "data.make" && name != "selected")
      return 0;
    Node node;
    node.type = type;
    node.name = StringAttr::get(entry.getContext(), name);
    node.attributes = attributes;
    node.coordinate = coordinate;
    node.complete = complete;
    append_range(node.operands, inputs);
    return intern(std::move(node));
  }
  Term uniformArm(ArrayRef<Term> inputs) {
    if (inputs.size() > 1 && inputs[1] &&
        all_of(inputs.drop_front(),
               [&](Term value) { return value == inputs[1]; }))
      return inputs[1];
    return 0;
  }
  Term selectedObservation(Node node) {
    // An observation shared by every arm does not depend on the selector.
    // Unknown arms (zero terms) cannot establish this agreement.
    if (Term common = uniformArm(node.operands))
      return common;
    node.complete = all_of(node.operands, [&](Term value) {
      return value && nodes[value].complete;
    });
    return node.complete ? intern(std::move(node)) : 0;
  }
  Term tag(Term term) {
    if (!term || !charge())
      return 0;
    if (observationDepth >= 64) {
      work.exhaust();
      return 0;
    }
    ++observationDepth;
    auto cleanup = scope_exit([&] { --observationDepth; });
    Node node = nodes[term];
    if (node.kind == Node::Input || node.kind == Node::Carry ||
        node.kind == Node::Exit) {
      node.tagOnly = true;
      return intern(std::move(node));
    }
    if (node.name && node.name.getValue() == "data.make")
      return expression("variant_tag", node.type, node.attributes, {});
    if (node.name && node.name.getValue() == "selected") {
      for (Term &arm : MutableArrayRef(node.operands).drop_front())
        arm = tag(arm);
      return selectedObservation(std::move(node));
    }
    return expression("variant_tag", node.type, {}, {term});
  }
  Term payload(Term term, unsigned alternative, unsigned index, Type type) {
    if (!term || !charge())
      return 0;
    if (observationDepth >= 64) {
      work.exhaust();
      return 0;
    }
    ++observationDepth;
    auto cleanup = scope_exit([&] { --observationDepth; });
    Node node = nodes[term];
    if ((node.kind == Node::Input || node.kind == Node::Carry ||
         node.kind == Node::Exit) &&
        !node.tagOnly && !node.extentAxis) {
      node.type = type;
      node.input.path.push_back(alternative);
      node.input.path.push_back(index);
      if (node.kind != Node::Input)
        node.projectionTypes.push_back(type);
      return intern(std::move(node));
    }
    if (node.name && node.name.getValue() == "data.make") {
      auto variant = dyn_cast<data::VariantType>(node.type);
      auto label = node.attributes.getAs<StringAttr>("alternative");
      if (!variant || alternative >= variant.getAlternatives().size())
        return 0;
      if (variant.getAlternatives()[alternative].getLabel() != label) {
        // Payload observations are guarded by their alternative. A closed
        // different constructor has no active payload obligation on this path;
        // it is not an unknown value. Selected joins still compare their tags.
        Node inactive;
        inactive.name = StringAttr::get(entry.getContext(), "inactive_payload");
        inactive.type = type;
        inactive.attributes = node.attributes;
        inactive.alternative = alternative;
        inactive.coordinate = index;
        return intern(std::move(inactive));
      }
      if (index >= node.operands.size())
        return 0;
      return node.operands[index];
    }
    if (node.name && node.name.getValue() == "selected") {
      for (Term &arm : MutableArrayRef(node.operands).drop_front())
        arm = payload(arm, alternative, index, type);
      node.type = type;
      return selectedObservation(std::move(node));
    }
    if (!node.complete)
      return 0;
    Node result;
    result.name = StringAttr::get(entry.getContext(), "variant_payload");
    result.type = type;
    result.alternative = alternative;
    result.coordinate = index;
    result.operands.push_back(term);
    return intern(std::move(result));
  }
  Term extent(Term term, Type type, unsigned axis) {
    auto collection = dyn_cast<CollectionTypeInterface>(type);
    if (!collection || !charge())
      return 0;
    if (observationDepth >= 64) {
      work.exhaust();
      return 0;
    }
    ++observationDepth;
    auto cleanup = scope_exit([&] { --observationDepth; });
    auto integer =
        IntegerType::get(entry.getContext(), 64, IntegerType::Unsigned);
    if (auto size = collection.getStaticExtent(axis)) {
      NamedAttribute value(StringAttr::get(entry.getContext(), "value"),
                           IntegerAttr::get(integer, *size));
      return expression("data.index", integer,
                        DictionaryAttr::get(entry.getContext(), value), {});
    }
    if (!term)
      return 0;
    Node node = nodes[term];
    if ((node.kind == Node::Input || node.kind == Node::Carry ||
         node.kind == Node::Exit) &&
        !node.tagOnly && !node.extentAxis) {
      node.extentAxis = axis;
      return intern(std::move(node));
    }
    if (node.name && node.name.getValue() == "selected") {
      for (Term &arm : MutableArrayRef(node.operands).drop_front())
        arm = extent(arm, type, axis);
      node.type = integer;
      return selectedObservation(std::move(node));
    }
    return expression("collection_extent", integer, {}, {term}, axis);
  }
  Term observe(Term value, const Node &observation) {
    if (!charge(1 + observation.input.path.size()))
      return 0;
    for (unsigned i = 0; i < observation.projectionTypes.size(); ++i)
      value = payload(value, observation.input.path[2 * i],
                      observation.input.path[2 * i + 1],
                      observation.projectionTypes[i]);
    if (observation.tagOnly)
      value = tag(value);
    if (observation.extentAxis)
      value = extent(value, observation.type, *observation.extentAxis);
    return value;
  }
  std::optional<uint64_t> constantCount(Term term) {
    if (!term || !charge())
      return std::nullopt;
    const Node &node = nodes[term];
    if (node.name && node.name.getValue() == "data.index")
      if (auto value = node.attributes.getAs<IntegerAttr>("value"))
        return value.getValue().getZExtValue();
    return std::nullopt;
  }
  std::optional<unsigned> selectedArm(Term selector, ArrayAttr alternatives) {
    if (!selector || !charge())
      return std::nullopt;
    const Node &node = nodes[selector];
    if (!node.name)
      return std::nullopt;
    if (node.name.getValue() == "arith.constant" &&
        node.type.isSignlessInteger(1))
      if (auto value = node.attributes.getAs<IntegerAttr>("value"))
        return value.getValue().getBoolValue() ? 0 : 1;
    if (node.name.getValue() == "data.make")
      if (auto label = node.attributes.getAs<StringAttr>("alternative"))
        for (auto [index, alternative] : enumerate(alternatives)) {
          if (!charge())
            return std::nullopt;
          if (label == alternative)
            return index;
        }
    return std::nullopt;
  }
  bool equal(Term lhs, Term rhs, Operation *control,
             std::set<std::pair<Term, Term>> &seen) {
    SmallVector<std::pair<Term, Term>> pending{{lhs, rhs}};
    while (!pending.empty()) {
      auto [left, right] = pending.pop_back_val();
      if (!charge() || !left || !right)
        return false;
      if (!nodes[left].complete || !nodes[right].complete)
        return false;
      if (left == right || !seen.insert({left, right}).second)
        continue;
      // Observing an equation can intern more terms and reallocate nodes.
      const Node a = nodes[left], b = nodes[right];
      if (a.type != b.type || a.kind != b.kind)
        return false;
      if (a.kind == Node::Input) {
        if (a.tagOnly != b.tagOnly || a.extentAxis != b.extentAxis)
          return false;
        bool known = false;
        for (const auto &requirement : requirements) {
          if (!charge())
            return false;
          const auto &x = requirement.components[0];
          const auto &y = requirement.components[1];
          auto same = [](const CommonControlComponent &p,
                         const CommonControlComponent &q) {
            return p.input == q.input && p.role == q.role && p.path == q.path;
          };
          known |= requirement.type == a.type &&
                   requirement.tagOnly == a.tagOnly &&
                   requirement.extentAxis == a.extentAxis &&
                   ((same(x, a.input) && same(y, b.input)) ||
                    (same(y, a.input) && same(x, b.input)));
        }
        if (!known) {
          if (!charge(a.input.path.size() + b.input.path.size() + 2))
            return false;
          requirements.push_back(
              {{a.input, b.input}, a.type, a.tagOnly, a.extentAxis, control});
        }
        continue;
      }
      if (a.kind == Node::Carry || a.kind == Node::Exit ||
          a.kind == Node::Iteration) {
        if (a.invocation != b.invocation || a.coordinate != b.coordinate ||
            a.input.path != b.input.path || a.tagOnly != b.tagOnly ||
            a.extentAxis != b.extentAxis ||
            a.projectionTypes != b.projectionTypes)
          return false;
        if (a.kind == Node::Iteration)
          continue; // Its invocation's count has an independent demand.
        const auto &loop = recurrences[a.invocation];
        auto enqueue = [&](const Components &values) {
          pending.emplace_back(observe(values[a.role], a),
                               observe(values[b.role], b));
        };
        // A repeated pair closes a guarded induction hypothesis only. Both
        // base and step remain on this worklist, so neither an ungrounded
        // cycle nor a failing sibling equation can establish agreement.
        enqueue(loop.initial[a.coordinate]);
        if (a.kind == Node::Exit || !loop.atMostOne)
          enqueue(loop.transition[a.coordinate]);
        if (a.kind == Node::Exit)
          pending.emplace_back(loop.count[a.role], loop.count[b.role]);
        continue;
      }
      if (a.name != b.name || a.attributes != b.attributes ||
          a.coordinate != b.coordinate || a.alternative != b.alternative ||
          a.operands.size() != b.operands.size() || !charge(a.operands.size()))
        return false;
      for (auto [x, y] : zip(a.operands, b.operands))
        pending.emplace_back(x, y);
    }
    return true;
  }
  const Components &components(const Environment &environment,
                               Value value) const {
    return environment.find(value)->second;
  }
  Expected<SmallVector<unsigned>> roster(ArrayAttr names,
                                         const StringMap<unsigned> &mapping) {
    SmallVector<unsigned> result;
    if (!names || !charge(names.size()))
      return failure();
    for (Attribute item : names) {
      auto name = dyn_cast<StringAttr>(item);
      auto found = name ? mapping.find(name.getValue()) : mapping.end();
      if (found == mapping.end() || is_contained(result, found->second))
        return failure();
      result.push_back(found->second);
    }
    return result;
  }
  Error common(Operation *op, Value selector, ArrayRef<unsigned> selected,
               Environment &environment, bool tagOnly = false) {
    if (selected.size() < 2)
      return Error::success();
    auto values = components(environment, selector);
    if (values.size() != roles)
      return failure();
    Term first =
        tagOnly ? tag(values[selected.front()]) : values[selected.front()];
    for (unsigned role : selected.drop_front()) {
      Term next = tagOnly ? tag(values[role]) : values[role];
      if (!charge())
        return failure();
      demands.push_back({first, next, op});
    }
    return Error::success();
  }
  Expected<SmallVector<Components>> block(Block &body, Environment &environment,
                                          const StringMap<unsigned> &mapping,
                                          unsigned depth) {
    if (depth >= 64) {
      work.exhaust();
      return failure();
    }
    for (Operation &operation : body) {
      auto *op = &operation;
      if (!charge(1 + uint64_t(roles + 1) *
                          (op->getNumOperands() + op->getNumResults())))
        return failure();
      if (op->hasTrait<OpTrait::IsTerminator>()) {
        SmallVector<Components> result;
        for (Value value : op->getOperands())
          result.push_back(components(environment, value));
        return result;
      }
      if (isa<pir::BranchOp, data::BranchOp>(op)) {
        SmallVector<unsigned> selected;
        if (auto branch = dyn_cast<pir::BranchOp>(op)) {
          auto resolved = roster(branch.getRoles(), mapping);
          if (!resolved)
            return resolved.takeError();
          selected = std::move(*resolved);
          if (auto e =
                  common(op, op->getOperand(0), selected, environment,
                         !op->getOperand(0).getType().isSignlessInteger(1)))
            return std::move(e);
        }
        SmallVector<SmallVector<Components>> arms;
        for (auto [index, region] : enumerate(op->getRegions())) {
          auto types = selectedPayloadTypes(op, index);
          if (!types)
            return types.takeError();
          if (!charge(uint64_t(roles) * region.front().getNumArguments()))
            return failure();
          Environment inner;
          auto selector = components(environment, op->getOperand(0));
          for (auto [port, argument] :
               enumerate(region.front().getArguments())) {
            Components values = absent();
            for (unsigned role = 0; role < roles; ++role)
              values[role] =
                  port < types->size()
                      ? payload(selector[role], index, port, argument.getType())
                      : components(
                            environment,
                            op->getOperand(port - types->size() + 1))[role];
            inner[argument] = std::move(values);
          }
          auto result = block(region.front(), inner, mapping, depth + 1);
          if (!result)
            return result.takeError();
          arms.push_back(std::move(*result));
        }
        for (auto [index, result] : enumerate(op->getResults())) {
          Components values = absent();
          for (unsigned role = 0; role < roles; ++role) {
            Term selector = components(environment, op->getOperand(0))[role];
            if (auto chosen = selectedArm(
                    selector, op->getAttrOfType<ArrayAttr>("alternatives"))) {
              values[role] = arms[*chosen][index][role];
              continue;
            }
            Components inputs{op->getOperand(0).getType().isSignlessInteger(1)
                                  ? selector
                                  : tag(selector)};
            for (const auto &arm : arms)
              inputs.push_back(arm[index][role]);
            if (Term common = uniformArm(inputs))
              values[role] = common;
            else
              values[role] = expression("selected", result.getType(),
                                        op->getAttrDictionary(), inputs, index);
          }
          environment[result] = std::move(values);
        }
      } else if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        auto selected = roster(repeat.getRoles(), mapping);
        if (!selected)
          return selected.takeError();
        if (auto e = common(op, repeat.getInputs()[0], *selected, environment))
          return std::move(e);
        if (!charge(1 + uint64_t(roles) * (repeat.getCarried() + 1)))
          return failure();
        unsigned invocation = recurrences.size();
        Recurrence recurrence;
        recurrence.count = components(environment, repeat.getInputs()[0]);
        recurrence.atMostOne = repeat.getMaximum() <= 1;
        bool smallCount = true;
        for (unsigned role : *selected) {
          auto count = constantCount(recurrence.count[role]);
          smallCount &= count && *count <= 1;
        }
        recurrence.atMostOne |= smallCount;
        for (Value initial : repeat.getInputs().slice(1, repeat.getCarried()))
          recurrence.initial.push_back(components(environment, initial));
        recurrences.push_back(std::move(recurrence));
        Environment inner;
        auto &region = repeat.getBody().front();
        for (auto [index, argument] : enumerate(region.getArguments())) {
          Components values = absent();
          for (unsigned role : *selected) {
            if (index <= unsigned(repeat.getCarried())) {
              Node node;
              node.kind = index ? Node::Carry : Node::Iteration;
              node.type = argument.getType();
              node.invocation = invocation;
              node.coordinate = index ? index - 1 : 0;
              node.role = role;
              values[role] = intern(std::move(node));
            } else
              values[role] =
                  components(environment, op->getOperand(index))[role];
          }
          inner[argument] = std::move(values);
        }
        auto yielded = block(region, inner, mapping, depth + 1);
        if (!yielded)
          return yielded.takeError();
        recurrences[invocation].transition = std::move(*yielded);
        for (auto [index, result] : enumerate(repeat.getResults())) {
          Components values = absent();
          for (unsigned role : *selected) {
            auto count = constantCount(recurrences[invocation].count[role]);
            if ((count && *count == 0) || repeat.getMaximum() == 0)
              values[role] = recurrences[invocation].initial[index][role];
            else if (count && *count == 1)
              values[role] = recurrences[invocation].transition[index][role];
            else {
              Node node;
              node.kind = Node::Exit;
              node.type = result.getType();
              node.invocation = invocation;
              node.coordinate = index;
              node.role = role;
              values[role] = intern(std::move(node));
            }
          }
          environment[result] = std::move(values);
        }
      } else if (isa<pir::ApplyOp, func::CallOp>(op)) {
        auto ref = op->getAttrOfType<FlatSymbolRefAttr>("callee");
        Operation *callee =
            ref ? symbols.lookupNearestSymbolFrom(op, ref) : nullptr;
        if (!callee || !active.insert(callee).second ||
            callee->getNumRegions() != 1)
          return failure();
        auto cleanup = scope_exit([&] { active.erase(callee); });
        StringMap<unsigned> nested(mapping);
        if (auto application = dyn_cast<pir::ApplyOp>(op)) {
          auto formal = cast<pir::MathematicalOp>(callee);
          auto actual = roster(application.getRoles(), mapping);
          if (!actual)
            return actual.takeError();
          nested.clear();
          for (auto [role, index] : zip(formal.getRoles(), *actual))
            nested[cast<StringAttr>(role).getValue()] = index;
        }
        Environment inner;
        for (auto [argument, input] :
             zip(callee->getRegion(0).front().getArguments(),
                 op->getOperands()))
          inner[argument] = components(environment, input);
        auto outputs =
            block(callee->getRegion(0).front(), inner, nested, depth + 1);
        if (!outputs)
          return outputs.takeError();
        for (auto [result, components] : zip(op->getResults(), *outputs))
          environment[result] = std::move(components);
      } else if (auto view = dyn_cast<pir::RestrictRolesOp>(op)) {
        auto selected = roster(view.getRoles(), mapping);
        if (!selected)
          return selected.takeError();
        Components values = absent();
        for (unsigned role : *selected)
          values[role] = components(environment, view.getInput())[role];
        environment[view.getOutput()] = std::move(values);
      } else if (auto assembly = dyn_cast<pir::AssembleRolesOp>(op)) {
        auto selected = roster(assembly.getRoles(), mapping);
        if (!selected)
          return selected.takeError();
        Components values = absent();
        for (auto [role, input] : zip(*selected, assembly.getInputs()))
          values[role] = components(environment, input)[role];
        environment[assembly.getOutput()] = std::move(values);
      } else if (mathematical::isTotal(op)) {
        for (auto [index, result] : enumerate(op->getResults())) {
          Components values = absent();
          for (unsigned role = 0; role < roles; ++role) {
            Components inputs;
            for (Value input : op->getOperands())
              inputs.push_back(components(environment, input)[role]);
            if (auto dimension = dyn_cast<data::DimOp>(op))
              values[role] = extent(inputs[0], dimension.getInput().getType(),
                                    dimension.getAxis());
            else if (auto get = dyn_cast<data::GetOp>(op))
              values[role] =
                  payload(inputs[0], 0, get.getIndex(), result.getType());
            else {
              if (isa<data::IsOp>(op))
                inputs[0] = tag(inputs[0]);
              values[role] =
                  expression(op->getName().getStringRef(), result.getType(),
                             op->getAttrDictionary(), inputs, index);
            }
          }
          environment[result] = std::move(values);
        }
      } else {
        // Ordered outputs, services and received values have no total/static
        // provenance. Their mere availability never supplies agreement.
        for (Value result : op->getResults())
          environment[result] = absent();
      }
    }
    return failure();
  }
  Expected<SmallVector<CommonControlRequirement>> run() {
    roles = entry.getRoles().size();
    StringMap<unsigned> mapping;
    for (auto [index, role] : enumerate(entry.getRoles()))
      mapping[cast<StringAttr>(role).getValue()] = index;
    Environment environment;
    if (!charge(uint64_t(roles) * entry.getBody().front().getNumArguments()))
      return failure();
    for (auto [index, argument, placement] : enumerate(
             entry.getBody().front().getArguments(), entry.getInputRoles())) {
      Components values = absent();
      if (!isa<pir::ServiceReferenceType>(argument.getType()))
        for (Attribute role : cast<ArrayAttr>(placement)) {
          Node node;
          node.kind = Node::Input;
          node.type = argument.getType();
          node.input = {unsigned(index), cast<StringAttr>(role), {}};
          values[mapping.lookup(cast<StringAttr>(role).getValue())] =
              intern(std::move(node));
        }
      environment[argument] = std::move(values);
    }
    active.insert(entry);
    auto result = block(entry.getBody().front(), environment, mapping, 0);
    if (!result)
      return result.takeError();
    for (const auto &demand : demands) {
      std::set<std::pair<Term, Term>> seen;
      if (!equal(demand.left, demand.right, demand.control, seen))
        return failure();
    }
    if (work.exhausted())
      return failure();
    return std::move(requirements);
  }
};
} // namespace
Expected<SmallVector<CommonControlRequirement>>
deriveCommonControlRequirements(pir::MathematicalOp entry, facts::Work &work) {
  if (!entry || !work.charge())
    return error(work.exhausted() ? "common-control-capacity"
                                  : "common-control-provenance");
  Derivation derivation{entry, work};
  return derivation.run();
}
} // namespace zkc
