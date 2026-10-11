#include "BindingWitness.h"
#include "ScopedWitness.h"
#include <algorithm>
#include <tuple>
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct Origin {
  uint32_t binding;
  std::vector<unsigned> path;
  bool operator==(const Origin &other) const {
    return binding == other.binding && path == other.path;
  }
  bool operator!=(const Origin &other) const { return !(*this == other); }
};
using Origins = std::vector<std::optional<Origin>>;
using SpanKey = std::tuple<uint32_t, uint32_t, uint32_t>;
SpanKey key(Span span) { return {span.source.index, span.begin, span.end}; }

// Independently relate source place reads and authored call operands to the
// checked SSA graph. Projection provenance is reconstructed from operations,
// never from the producer's binding environment or a re-elaborated Body.
class ValueCheck {
  Semantics &types;
  const CheckedStorage &storage;
  const ScopedSource &source;
  const SyntaxDeclaration &syntax;
  const Declaration &owner;
  std::set<uint32_t> expectedReads, observedReads;
  std::set<uint32_t> expectedNotations, observedNotations;
  std::map<SpanKey, uint32_t> aliases;
  bool refuse(Span span) {
    return types.fail("source.scoped-witness",
                      "scoped value use differs from its authored expression",
                      span);
  }
  bool bounded(unsigned depth, Span span) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "scoped value witness depth", span);
    return types.charge(1, span);
  }
  std::optional<Origin> place(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions.at(id);
    if (!bounded(depth, expr.span))
      return {};
    if (expr.kind == Expression::Kind::Name) {
      if (expr.binding && source.environment.count(*expr.binding))
        return Origin{expr.binding->index, {}};
      return {};
    }
    if (expr.kind != Expression::Kind::Projection &&
        expr.kind != Expression::Kind::Subscript)
      return {};
    auto root = place(expr.children.front(), depth + 1);
    if (!root)
      return {};
    auto type = types.projectedType(
        owner, source.environment.at(BindingId{root->binding}).type, root->path,
        expr.span);
    if (type && expr.kind == Expression::Kind::Subscript &&
        type->kind != Type::Kind::Array)
      return {};
    auto label = expr.kind == Expression::Kind::Subscript
                     ? staticSubscriptIndex(syntax, expr)
                     : std::optional<StringRef>(expr.text);
    if (!label) {
      refuse(expr.span);
      return {};
    }
    auto index =
        type ? types.fieldIndex(owner, *type, *label, expr.span) : std::nullopt;
    if (!index)
      return {};
    root->path.push_back(*index);
    return root;
  }
  bool collect(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions.at(id);
    if (!bounded(depth, expr.span))
      return false;
    if (source.notationFamilies && source.notationFamilies->count(id))
      expectedNotations.insert(id);
    if (place(id, depth)) {
      expectedReads.insert(id);
      return true;
    }
    if (types.diagnostic)
      return false;
    for (auto child : expr.children)
      if (!collect(child, depth + 1))
        return false;
    for (auto region : expr.regions) {
      const auto &block = syntax.bodies.at(region);
      for (const auto &statement : block.statements) {
        if (!collect(statement.expression, depth + 1))
          return false;
        if (statement.kind == Statement::Kind::Let &&
            statement.pattern.kind == Pattern::Kind::Name)
          aliases.emplace(key(statement.pattern.span), statement.expression);
        if (statement.kind == Statement::Kind::Assign)
          aliases.emplace(key(statement.span), statement.expression);
      }
      for (const auto &[name, result] : block.results)
        if (!collect(result, depth + 1))
          return false;
    }
    return true;
  }
  bool body(const Body &body, Origins origins, unsigned depth) {
    const auto &expressionValues = body.expressionValues;
    if (!bounded(depth, {}) ||
        !types.charge(body.values.size() + body.operations.size() +
                          expressionValues.size(),
                      {}))
      return false;
    if (origins.size() != body.inputs)
      return refuse({});
    origins.resize(body.values.size());
    std::vector<const Operation *> producers(body.values.size());
    std::set<const Operation *> checkedCalls;
    for (const auto &op : body.operations) {
      if (std::holds_alternative<HelperCall>(op.action) && !op.binding)
        return refuse(op.span);
      for (auto value : op.results) {
        if (value.index < body.inputs || value.index >= producers.size() ||
            producers[value.index])
          return refuse(op.span);
        producers[value.index] = &op;
      }
      if (const auto *projection = std::get_if<Projection>(&op.action)) {
        if (projection->input.index >= origins.size() || op.results.size() != 1)
          return refuse(op.span);
        auto origin = origins[projection->input.index];
        if (origin) {
          if (!types.charge(origin->path.size() + projection->path.size() + 1,
                            op.span))
            return false;
          origin->path.insert(origin->path.end(), projection->path.begin(),
                              projection->path.end());
        }
        origins[op.results.front().index] = std::move(origin);
        auto alias = aliases.find(key(op.span));
        if (alias != aliases.end()) {
          auto expected = expressionValues.find(alias->second);
          if (expected != expressionValues.end() &&
              (!projection->path.empty() ||
               projection->input.index != expected->second.index))
            return refuse(op.span);
        }
      }
    }
    auto value = [&](uint32_t expression) -> std::optional<ValueId> {
      auto found = expressionValues.find(expression);
      if (found == expressionValues.end())
        return {};
      return found->second;
    };
    auto arguments = [&](ArrayRef<ValueId> operands, const Expression &expr) {
      if (operands.size() != expr.children.size())
        return refuse(expr.span);
      for (unsigned i = 0; i < operands.size(); ++i) {
        auto expected = value(expr.children[i]);
        if (!expected || expected->index != operands[i].index)
          return refuse(expr.span);
      }
      return true;
    };
    for (const auto &[id, actual] : expressionValues) {
      if (id >= syntax.expressions.size() || actual.index >= origins.size())
        return refuse({});
      const auto &expr = syntax.expressions[id];
      if (!bounded(depth, expr.span))
        return false;
      if (auto expected = place(id, depth)) {
        if (origins[actual.index] != expected)
          return refuse(expr.span);
        observedReads.insert(id);
      }
      if (types.diagnostic)
        return false;
      const auto *op = producers[actual.index];
      if (expectedNotations.count(id)) {
        if (!op || !op->binding || key(op->span) != key(expr.span) ||
            !observedNotations.insert(id).second)
          return refuse(expr.span);
      }
      if (!op || key(op->span) != key(expr.span))
        continue;
      if (op->binding) {
        checkedCalls.insert(op);
        const auto &binding = *op->binding;
        if (binding.target.declaration.index >= storage.declarations.size())
          return refuse(expr.span);
        const auto &callee =
            storage.declarations[binding.target.declaration.index];
        auto inputOrder = callee.inputOrder;
        if (inputOrder.empty())
          for (unsigned i = 0; i < callee.inputs.size(); ++i)
            inputOrder.push_back({Declaration::InputSlot::Kind::Data, i});
        if (expr.children.size() != inputOrder.size())
          return refuse(expr.span);
        for (unsigned i = 0; i < expr.children.size(); ++i) {
          unsigned parameter = i;
          for (const auto &label : expr.callLabels)
            if (label.index == i) {
              parameter = inputOrder.size();
              for (unsigned j = 0; j < inputOrder.size(); ++j) {
                const auto &slot = inputOrder[j];
                const auto &name =
                    slot.kind == Declaration::InputSlot::Kind::Data
                        ? callee.inputs[slot.index].name
                    : slot.kind == Declaration::InputSlot::Kind::Scoped
                        ? callee.scopedInputs[slot.index].name
                        : callee.domainInputs[slot.index].name;
                if (name == label.name)
                  parameter = j;
              }
            }
          if (parameter >= inputOrder.size())
            return refuse(expr.span);
          const auto &slot = inputOrder[parameter];
          if (slot.kind != Declaration::InputSlot::Kind::Data)
            continue;
          auto expected = value(expr.children[i]);
          if (slot.index >= binding.operands.size() || !expected ||
              expected->index != binding.operands[slot.index].index)
            return refuse(expr.span);
        }
        if (!checkCallAction(types, storage.declarations, body, *op))
          return false;
        if (expr.kind == Expression::Kind::NotationCall ||
            expr.kind == Expression::Kind::Subscript || binding.notation) {
          if (!expr.notation || !binding.notation || !source.notationFamilies ||
              !source.notationFamilies->count(id) || !expr.scope ||
              *expr.scope >= syntax.bodies.size() ||
              !syntax.bodies[*expr.scope].notationEnvironment ||
              !checkNotationOccurrence(
                  types, expr, *syntax.bodies[*expr.scope].notationEnvironment))
            return types.diagnostic ? false : refuse(expr.span);
          // Scoped/domain binders carry their own complete argument categories
          // and are rechecked by ScopedWitness. Here ordinary data calls retain
          // the same independent family and operand check.
          if (expr.notation->position !=
              NotationDescriptor::Position::Reduction) {
            std::vector<Type> inputs;
            std::vector<unsigned> order;
            std::vector<ValueId> authored;
            for (unsigned i = 0; i < binding.operands.size(); ++i) {
              auto operand = binding.operands[i];
              if (operand.index >= body.values.size())
                return refuse(expr.span);
              inputs.push_back(body.values[operand.index].type);
              order.push_back(i);
              auto expected = value(expr.children[i]);
              if (!expected)
                return refuse(expr.span);
              authored.push_back(*expected);
            }
            if (!checkOperatorOperands(types, *expr.notation, binding, order,
                                       authored, expr.span) ||
                !checkOperatorWitness(
                    types, storage.declarations,
                    source.notationFamilies->at(id), *expr.notation, binding,
                    inputs, body.values[actual.index].type, expr.span))
              return false;
          }
        }
      } else if (const auto *invoke = std::get_if<ScopedInvoke>(&op->action)) {
        if (!arguments(invoke->operands, expr))
          return false;
      } else if (const auto *math = std::get_if<MathValue>(&op->action)) {
        if (expr.kind == Expression::Kind::Intrinsic &&
            !arguments(math->operands, expr))
          return false;
      } else if (const auto *primitive =
                     std::get_if<LocalPrimitive>(&op->action)) {
        if ((expr.kind == Expression::Kind::Kernel) !=
            (primitive->origin == LocalPrimitive::Origin::Kernel))
          return refuse(expr.span);
        if (expr.kind == Expression::Kind::Kernel &&
            !arguments(primitive->operands, expr))
          return false;
      } else if (const auto *construct = std::get_if<Construct>(&op->action)) {
        if ((expr.kind == Expression::Kind::Tuple ||
             expr.kind == Expression::Kind::Array ||
             (expr.kind == Expression::Kind::Call && expr.text == "unpack")) &&
            !arguments(construct->operands, expr))
          return false;
      }
    }
    for (const auto &op : body.operations) {
      if (op.binding && !checkedCalls.count(&op))
        return refuse(op.span);
      if (const auto *control = std::get_if<LocalControl>(&op.action)) {
        unsigned head = control->kind == LocalControl::Kind::For ? 2 : 1;
        if (control->operands.size() < head)
          return refuse(op.span);
        unsigned captured = control->operands.size() - head;
        for (const auto &region : control->regions) {
          if (region->inputs < captured)
            return refuse(op.span);
          Origins nested(region->inputs);
          for (unsigned i = 0; i < captured; ++i) {
            auto operand = control->operands[head + i];
            if (operand.index >= origins.size())
              return refuse(op.span);
            nested[region->inputs - captured + i] = origins[operand.index];
          }
          if (!this->body(*region, std::move(nested), depth + 1))
            return false;
        }
      }
    }
    for (const auto &binding : body.scopedBindings) {
      if (!binding.computation)
        continue;
      const auto &computation = *binding.computation;
      Origins nested(computation.body->inputs);
      unsigned explicitInputs = computation.signature.inputs.size();
      if (nested.size() != explicitInputs + binding.captures.size())
        return refuse(binding.span);
      for (unsigned i = 0; i < binding.captures.size(); ++i) {
        auto capture = binding.captures[i];
        if (capture.index >= origins.size())
          return refuse(binding.span);
        nested[explicitInputs + i] = origins[capture.index];
      }
      if (!this->body(*computation.body, std::move(nested), depth + 1))
        return false;
    }
    return true;
  }

public:
  ValueCheck(Semantics &types, const CheckedStorage &storage,
             const ScopedSource &source)
      : types(types), storage(storage), source(source), syntax(*source.syntax),
        owner(storage.declarations[source.owner.index]) {}
  bool run(const ScopedBinding &binding) {
    const auto &computation = *binding.computation;
    Origins inputs(computation.body->inputs);
    auto count = computation.signature.inputs.size();
    if (inputs.size() != count + computation.captures.size())
      return refuse(binding.span);
    for (unsigned i = 0; i < computation.captures.size(); ++i) {
      const auto &capture = computation.captures[i];
      inputs[count + i] = Origin{capture.binding, capture.path};
    }
    const auto &authored = syntax.expressions.at(source.expression);
    const auto &region = syntax.bodies.at(authored.regions.front());
    const auto &checked = *computation.body;
    if (!checked.stopped && !region.results.empty()) {
      auto result =
          checked.expressionValues.find(region.results.front().second);
      if (region.results.size() != 1 || checked.results.size() != 1 ||
          result == checked.expressionValues.end() ||
          checked.results.front().index != result->second.index)
        return refuse(binding.span);
    }
    return collect(source.expression, 1) &&
           body(*computation.body, std::move(inputs), 1) &&
           ((observedReads == expectedReads &&
             observedNotations == expectedNotations) ||
            refuse(binding.span));
  }
};
} // namespace
bool checkScopedValues(Semantics &types, const CheckedStorage &storage,
                       const ScopedSource &source,
                       const ScopedBinding &binding) {
  return ValueCheck(types, storage, source).run(binding);
}
} // namespace zkc::language::detail
