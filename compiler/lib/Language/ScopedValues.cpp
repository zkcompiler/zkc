#include "BindingWitness.h"
#include "FreePlaces.h"
#include "ScopedWitness.h"
#include <algorithm>
#include <tuple>
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct Origin {
  uint32_t binding;
  std::vector<unsigned> path;
  uint64_t generation = 0;
  bool samePlace(const Origin &other) const {
    return binding == other.binding && path == other.path;
  }
  bool operator==(const Origin &other) const {
    return samePlace(other) && generation == other.generation;
  }
  bool operator!=(const Origin &other) const { return !(*this == other); }
};
using Origins = std::vector<std::optional<Origin>>;
using OriginTree = std::map<std::vector<unsigned>, Origin>;
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
  bool wholeBody = false;
  std::map<BindingId, Type> environment;
  using Alias = SourceOccurrences::Binding;
  const SourceOccurrences *occurrences = nullptr;
  std::map<const Operation *, const Alias *> authenticatedBindings;
  std::map<const Body *, std::vector<std::pair<unsigned, BindingId>>>
      inputBindings;
  std::vector<std::pair<BindingId, const Type *>> proposedTypes;
  std::set<uint32_t> expectedReads, observedReads;
  std::set<uint32_t> expectedNotations, observedNotations;
  std::set<uint32_t> expectedProducers, observedProducers;
  std::map<SpanKey, uint32_t> aliases;
  std::set<SpanKey> authoredDefinitions;
  std::map<uint32_t, std::set<uint32_t>> stateWrites;
  std::map<uint32_t, RegionInputs> sourceInputs;
  // Authored evaluation events, independent of the proposed operation order.
  // Regions share coordinates, but each authenticated body has its own events.
  struct Events {
    uint64_t read = 0, capture = 0, finish = 0;
    const SourceControlSnapshot *snapshot = nullptr;
  };
  std::vector<Events> events;
  std::map<SpanKey, uint64_t> definitionEvents;
  uint64_t nextEvent = 0, sourceLevels = 1;
  struct ValueIndex {
    std::vector<const Operation *> producers;
    std::vector<ValueId> identities;
    // Unlike general SSA identity, recipe identity also preserves availability
    // on every immediate edge. Invalidity survives endpoint restoration.
    std::vector<std::optional<ValueId>> recipeIdentities;
    Origins origins;
    std::map<uint32_t, std::set<uint64_t>> generations;
    std::vector<const Construct *> aggregates;
    std::optional<Span> invalidStateJoin;
  };
  // One index per actual candidate body for this replay only. Identity edges
  // are normalized in SSA order, so yield checks never rescan producer trees.
  std::map<const Body *, ValueIndex> indices;
  bool
  refuse(Span span,
         StringRef message = "value use differs from its authored expression") {
    return types.fail(wholeBody ? "source.binding-witness"
                                : "source.scoped-witness",
                      message, span);
  }
  bool bounded(unsigned depth, Span span) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "scoped value witness depth", span);
    return types.charge(1, span);
  }
  bool chargeOrigin(const std::optional<Origin> &origin, Span span) {
    return types.charge(origin ? origin->path.size() + 1 : 1, span);
  }
  bool chargeTree(const OriginTree &tree, Span span) {
    if (!types.charge(tree.size() + 1, span))
      return false;
    for (const auto &[path, origin] : tree)
      if (!types.charge(path.size() + origin.path.size() + 1, span))
        return false;
    return true;
  }
  std::optional<Origin> place(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions.at(id);
    if (!bounded(depth, expr.span))
      return {};
    if (expr.kind == Expression::Kind::Name) {
      if (!expr.binding)
        return {};
      if (wholeBody) {
        if (expr.binding->index >= syntax.bindings.size()) {
          refuse(expr.span);
          return {};
        }
        const auto &binding = syntax.bindings[expr.binding->index];
        if (binding.service || binding.scoped || binding.domain)
          return {};
        if (!environment.count(*expr.binding)) {
          refuse(expr.span, "authored data binding has no candidate value");
          return {};
        }
      }
      if (environment.count(*expr.binding))
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
        owner, environment.at(BindingId{root->binding}), root->path, expr.span);
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
  bool prepare(const Body &body, unsigned depth) {
    if (!bounded(depth, {}))
      return false;
    auto context = occurrences->candidates.find(&body);
    if (context == occurrences->candidates.end())
      return refuse({}, "missing authenticated body region");
    auto expected = occurrences->bindings.find(context->second);
    unsigned count =
        expected == occurrences->bindings.end() ? 0 : expected->second.size();
    uint64_t levels = 1;
    for (auto size = count; size > 1; size >>= 1)
      ++levels;
    if (!types.charge(2 * count * levels + body.operations.size() + 1, {}))
      return false;
    std::map<SpanKey, const Alias *> definitions;
    std::set<const Alias *> observed;
    if (expected != occurrences->bindings.end())
      for (const auto &definition : expected->second) {
        if (definition.input) {
          if (!definition.parameter || *definition.parameter >= body.inputs ||
              *definition.parameter >= body.values.size() ||
              key(body.values[*definition.parameter].span) !=
                  key(definition.span))
            return refuse(definition.span, "lexical input coverage differs");
          observed.insert(&definition);
          inputBindings[&body].emplace_back(*definition.parameter,
                                            definition.binding);
          proposedTypes.emplace_back(definition.binding,
                                     &body.values[*definition.parameter].type);
        } else {
          authoredDefinitions.insert(key(definition.span));
          if (!definitions.emplace(key(definition.span), &definition).second)
            return refuse(definition.span,
                          "ambiguous authored binding occurrence");
        }
      }
    for (const auto &op : body.operations) {
      const auto *projection = std::get_if<Projection>(&op.action);
      if (!projection || !projection->path.empty())
        continue;
      if (!types.charge(levels, op.span))
        return false;
      auto found = definitions.find(key(op.span));
      if (found == definitions.end())
        continue;
      const auto &definition = *found->second;
      if (op.results.size() != 1 || op.results.front().index < body.inputs ||
          op.results.front().index >= body.values.size() ||
          key(body.values[op.results.front().index].span) !=
              key(definition.span) ||
          !observed.insert(&definition).second)
        return refuse(op.span, "binding occurrence coverage differs");
      authenticatedBindings.emplace(&op, &definition);
      proposedTypes.emplace_back(definition.binding,
                                 &body.values[op.results.front().index].type);
    }
    if (observed.size() != count)
      return refuse({}, "binding occurrence coverage differs");
    for (const auto &op : body.operations) {
      if (const auto *control = std::get_if<LocalControl>(&op.action))
        for (const auto &region : control->regions)
          if (!prepare(*region, depth + 1))
            return false;
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        if (!prepare(*repeat->region, depth + 1))
          return false;
    }
    for (const auto &binding : body.scopedBindings)
      if (binding.computation &&
          !prepare(*binding.computation->body, depth + 1))
        return false;
    return true;
  }
  bool alias(const Body &body, const Operation &operation,
             const Alias &definition, ArrayRef<const Operation *> producers) {
    std::optional<ValueId> root;
    if (!types.charge(definition.path.size() + 1, operation.span))
      return false;
    for (const auto &selector : definition.path)
      if (!types.charge(selector.size(), operation.span))
        return false;
    auto selectors = definition.path;
    if (definition.parameter) {
      if (*definition.parameter >= body.inputs)
        return refuse(operation.span);
      root = ValueId{*definition.parameter};
    } else if (definition.expression) {
      auto found = body.expressionValues.find(*definition.expression);
      if (found != body.expressionValues.end())
        root = found->second;
      else {
        // Protocol applications have separate result ports, including zero
        // results. Their source expression is not an ordinary tuple value.
        const auto &expr = syntax.expressions[*definition.expression];
        if (!types.charge(body.operations.size(), operation.span))
          return false;
        for (const auto &op : body.operations)
          if ((std::holds_alternative<ProtocolApplication>(op.action) ||
               (expr.kind == Expression::Kind::FinishIf &&
                std::holds_alternative<ProtocolCompletion>(op.action))) &&
              key(op.span) == key(expr.span)) {
            unsigned port = 0;
            if (op.results.size() != 1) {
              if (selectors.empty() ||
                  StringRef(selectors.front()).getAsInteger(10, port))
                return refuse(operation.span);
              selectors.erase(selectors.begin());
            }
            if (port >= op.results.size())
              return refuse(operation.span);
            root = op.results[port];
          }
      }
    }
    if (!root || root->index >= body.values.size())
      return refuse(operation.span, "binding initializer has no source value");
    std::vector<unsigned> expected;
    if (!types.chargeType(body.values[root->index].type, operation.span))
      return false;
    auto type = body.values[root->index].type;
    for (const auto &selector : selectors) {
      auto index = types.fieldIndex(owner, type, selector, operation.span);
      if (!index)
        return false;
      expected.push_back(*index);
      auto projected =
          types.projectedType(owner, type, {*index}, operation.span);
      if (!projected)
        return false;
      type = *projected;
    }
    auto current = operation.results.front();
    std::vector<unsigned> actual;
    unsigned depth = 0;
    while (current.index != root->index) {
      if (!bounded(++depth, operation.span))
        return false;
      if (current.index >= producers.size())
        return refuse(operation.span,
                      "binding initializer producer is missing");
      auto *producer = producers[current.index];
      if (!producer)
        return refuse(operation.span,
                      "binding value differs from its initializer");
      if (const auto *projection = std::get_if<Projection>(&producer->action)) {
        if (!types.charge(actual.size() + projection->path.size() + 1,
                          operation.span))
          return false;
        actual.insert(actual.begin(), projection->path.begin(),
                      projection->path.end());
        current = projection->input;
      } else if (const auto *restriction =
                     std::get_if<Restriction>(&producer->action))
        current = restriction->input;
      else if (const auto *exchange = std::get_if<Exchange>(&producer->action);
               exchange && definition.exchange &&
               key(producer->span) == key(*definition.exchange))
        current = exchange->payload;
      else if (const auto *construct =
                   std::get_if<Construct>(&producer->action);
               construct && construct->kind == Construct::Kind::Unpack &&
               construct->operands.size() == 1)
        current = construct->operands.front();
      else
        return refuse(operation.span);
    }
    return actual == expected ||
           refuse(operation.span, "binding projection path differs");
  }
  bool definition(const Pattern &pattern, uint64_t event, unsigned depth) {
    if (!bounded(depth, pattern.span) ||
        !types.charge(sourceLevels, pattern.span))
      return false;
    definitionEvents.emplace(key(pattern.span), event);
    for (const auto &child : pattern.children)
      if (!definition(child, event, depth + 1))
        return false;
    return true;
  }
  bool collect(uint32_t id, unsigned depth,
               std::set<uint32_t> *writes = nullptr) {
    const auto &expr = syntax.expressions.at(id);
    if (!bounded(depth, expr.span))
      return false;
    if (wholeBody)
      events[id].read = ++nextEvent;
    if (expr.kind == Expression::Kind::And ||
        expr.kind == Expression::Kind::Or ||
        expr.kind == Expression::Kind::Boolean ||
        (expr.kind == Expression::Kind::Decimal && source.literals &&
         source.literals->count(id)) ||
        expr.kind == Expression::Kind::OracleQuery ||
        (source.enumTypes && source.enumTypes->count(id)))
      expectedProducers.insert(id);
    if (source.notationFamilies && source.notationFamilies->count(id))
      expectedNotations.insert(id);
    if (place(id, depth)) {
      expectedReads.insert(id);
      return true;
    }
    if (types.diagnostic)
      return false;
    std::set<uint32_t> nestedWrites, headerWrites;
    for (auto child : expr.children)
      if (!collect(child, depth + 1, &headerWrites))
        return false;
    if (wholeBody)
      events[id].capture = ++nextEvent;
    for (auto region : expr.regions) {
      const auto &block = syntax.bodies.at(region);
      for (const auto &statement : block.statements) {
        if (!collect(statement.expression, depth + 1, &nestedWrites))
          return false;
        if (wholeBody) {
          const auto event = ++nextEvent;
          if (!types.charge(sourceLevels, statement.span) ||
              !definition(statement.pattern, event, depth + 1))
            return false;
          definitionEvents.emplace(key(statement.span), event);
        }
        if (statement.kind == Statement::Kind::Let &&
            statement.pattern.kind == Pattern::Kind::Name)
          aliases.emplace(key(statement.pattern.span), statement.expression);
        if (statement.kind == Statement::Kind::Assign) {
          aliases.emplace(key(statement.span), statement.expression);
          if (statement.pattern.binding &&
              (!wholeBody || authoredDefinitions.count(key(statement.span)))) {
            if (!types.charge(1, statement.span))
              return false;
            nestedWrites.insert(statement.pattern.binding->index);
          }
        }
      }
      for (const auto &[name, result] : block.results)
        if (!collect(result, depth + 1, &nestedWrites))
          return false;
    }
    if (wholeBody)
      events[id].finish = ++nextEvent;
    uint64_t levels = 1;
    for (auto size = nestedWrites.size() + headerWrites.size() +
                     (writes ? writes->size() : 0);
         size > 1; size >>= 1)
      ++levels;
    if (!types.charge(2 * (nestedWrites.size() + headerWrites.size()) * levels +
                          1,
                      expr.span))
      return false;
    if (expr.kind == Expression::Kind::If ||
        expr.kind == Expression::Kind::Match ||
        expr.kind == Expression::Kind::For ||
        expr.kind == Expression::Kind::And || expr.kind == Expression::Kind::Or)
      for (auto binding : nestedWrites)
        if (binding < syntax.bindings.size() &&
            syntax.bindings[binding].span.begin < expr.span.begin)
          stateWrites[id].insert(binding);
    if (writes && expr.kind != Expression::Kind::Lambda) {
      writes->insert(nestedWrites.begin(), nestedWrites.end());
      writes->insert(headerWrites.begin(), headerWrites.end());
    }
    return true;
  }
  std::optional<ValueId> value(const Body &body, uint32_t id) {
    if (!types.charge(1, syntax.expressions[id].span))
      return {};
    auto found = body.expressionValues.find(id);
    if (found == body.expressionValues.end() ||
        found->second.index >= body.values.size()) {
      refuse(syntax.expressions[id].span, "authored result value is missing");
      return {};
    }
    return found->second;
  }
  bool sameValue(const Body &body, ValueId actual, ValueId expected) {
    const auto &index = indices.at(&body);
    return actual.index < index.identities.size() &&
           expected.index < index.identities.size() &&
           index.identities[actual.index].index ==
               index.identities[expected.index].index;
  }
  std::optional<ValueId> recipeRoot(const Body &body, ValueId value,
                                    const Operation &capture) {
    const auto &index = indices.at(&body);
    auto available = [&](ValueId id) {
      return id.index < body.values.size() &&
             (id.index < body.inputs ||
              (index.producers[id.index] &&
               index.producers[id.index] != &capture));
    };
    unsigned depth = 0;
    while (true) {
      if (!bounded(++depth, capture.span))
        return {};
      if (!available(value)) {
        refuse(capture.span, "recipe value is unavailable");
        return {};
      }
      auto identity = index.recipeIdentities[value.index];
      if (!identity) {
        refuse(capture.span,
               "recipe identity changes participant availability");
        return {};
      }
      if (identity->index != value.index) {
        value = *identity;
        continue;
      }
      const auto *producer = index.producers[value.index];
      const auto *restriction =
          producer ? std::get_if<Restriction>(&producer->action) : nullptr;
      if (!restriction)
        return value;
      if (producer->binding || producer->results.size() != 1 ||
          producer->results.front().index != value.index ||
          !available(restriction->input) ||
          (restriction->input.index >= body.inputs &&
           index.producers[restriction->input.index] >= producer)) {
        refuse(capture.span, "recipe restriction is unavailable");
        return {};
      }
      const auto &before = body.values[restriction->input.index];
      const auto &after = body.values[value.index];
      if (!types.chargeType(before.type, capture.span) ||
          !types.chargeType(after.type, capture.span) ||
          !types.charge(before.components.size() + after.components.size() +
                            restriction->roles.size() + 1,
                        capture.span))
        return {};
      auto data = [](const Value &value) {
        const auto *placement =
            value.placement
                ? std::get_if<DataPlacement>(&value.placement->value)
                : nullptr;
        return !value.oracleHolder &&
               (!value.placement ||
                (placement && placement->roles == value.components));
      };
      const auto &roles = restriction->roles;
      if (body.mode != Body::Mode::Protocol || before.type != after.type ||
          isLogicalValue(before.type) || !data(before) || !data(after) ||
          roles.empty() || roles.back() >= owner.roles.size() ||
          !std::is_sorted(roles.begin(), roles.end()) ||
          std::adjacent_find(roles.begin(), roles.end()) != roles.end() ||
          !std::is_sorted(before.components.begin(), before.components.end()) ||
          std::adjacent_find(before.components.begin(),
                             before.components.end()) !=
              before.components.end() ||
          after.components != roles ||
          !std::includes(before.components.begin(), before.components.end(),
                         roles.begin(), roles.end())) {
        refuse(capture.span, "recipe restriction differs from source value");
        return {};
      }
      if (!types.executableType(before.type, capture.span) ||
          !types.requireUsage(before.type, Usage::Drop, capture.span, &owner,
                              "source.permission",
                              "recipe restriction requires Drop"))
        return {};
      value = restriction->input;
    }
  }
  const Construct *aggregate(const Body &body, ValueId actual) {
    const auto &index = indices.at(&body);
    if (actual.index >= index.identities.size())
      return nullptr;
    return index.aggregates[index.identities[actual.index].index];
  }
  bool carrier(const Body &body, const Operation &op, ValueIndex &index) {
    const auto *pack = std::get_if<Construct>(&op.action);
    if (!pack || pack->kind != Construct::Kind::Aggregate || op.binding ||
        !pack->alternative.empty() || op.results.size() != 1)
      return true;
    const auto result = op.results.front();
    const auto &type = body.values[result.index].type;
    if (type.kind != Type::Kind::Unit && type.kind != Type::Kind::Tuple)
      return true; // Source arrays and nominal products are not tuple carriers.
    if (!types.chargeType(type, op.span) ||
        !types.charge(pack->operands.size() + 1, op.span))
      return false;
    if (pack->operands.size() != type.arguments.size() ||
        (type.kind == Type::Kind::Unit &&
         (type != Type(Type::Kind::Unit) || !pack->operands.empty())))
      return refuse(op.span, "administrative carrier arity differs");
    for (unsigned i = 0; i < pack->operands.size(); ++i) {
      auto operand = pack->operands[i];
      if (operand.index >= body.values.size() ||
          (operand.index >= body.inputs &&
           (!index.producers[operand.index] ||
            index.producers[operand.index] == &op)))
        return refuse(op.span, "administrative carrier operand is unavailable");
      const auto &actual = body.values[operand.index].type;
      if (!types.chargeType(actual, op.span))
        return false;
      if (actual != type.arguments[i])
        return refuse(op.span, "administrative carrier field type differs");
    }
    index.aggregates[result.index] = pack;
    return true;
  }
  bool unit(const Body &body, ValueId actual) {
    auto *pack = aggregate(body, actual);
    return actual.index < body.values.size() &&
           body.values[actual.index].type.kind == Type::Kind::Unit && pack &&
           pack->operands.empty();
  }
  std::optional<ValueId> tail(const Body &body) {
    auto context = occurrences->candidates.find(&body);
    if (context == occurrences->candidates.end()) {
      refuse({}, "missing authenticated yield region");
      return {};
    }
    if (context->second.second)
      return value(body, *context->second.second);
    const auto &written = syntax.bodies[context->second.first];
    if (written.results.size() == 1)
      return value(body, written.results.front().second);
    if (!written.results.empty())
      refuse(written.span, "authored region has several tails");
    return {};
  }
  bool returns(const Body &body, std::optional<uint32_t> callback) {
    if (body.stopped)
      return true;
    if (!wholeBody)
      return true; // The enclosing invocation replay owns region associations.
    if (callback) {
      auto expected = tail(body);
      if (body.results.size() == 1 &&
          (expected ? sameValue(body, body.results.front(), *expected)
                    : !types.diagnostic && unit(body, body.results.front())))
        return true;
      return types.diagnostic
                 ? false
                 : refuse({}, "callback yield differs from source");
    }
    const auto &written = syntax.bodies.front();
    if (!types.charge(written.results.size() + owner.outputs.size() + 1,
                      written.span))
      return false;
    if (body.results.size() != owner.outputs.size() ||
        written.results.size() != owner.outputs.size())
      return refuse(written.span, "return port coverage differs from source");
    std::map<StringRef, unsigned> ports;
    for (unsigned i = 0; i < owner.outputs.size(); ++i) {
      if (!types.charge(owner.outputs[i].name.size() + 1, written.span))
        return false;
      ports.emplace(owner.outputs[i].name, i);
    }
    std::set<unsigned> seen;
    for (const auto &[name, id] : written.results) {
      auto at = ports.find(name);
      if (body.mode == Body::Mode::Protocol && name.empty() &&
          ports.size() == 1)
        at = ports.begin();
      auto expected = value(body, id);
      if (at == ports.end() || !seen.insert(at->second).second || !expected ||
          !sameValue(body, body.results[at->second], *expected))
        return types.diagnostic
                   ? false
                   : refuse(written.span,
                            "return value differs from source tail");
    }
    return true;
  }
  bool header(const Body &body, const Operation &op, const Control &control) {
    if (!op.expression)
      return refuse(op.span);
    const auto &expr = syntax.expressions[*op.expression];
    unsigned count = control.kind == Control::Kind::For ? 2 : 1;
    if (expr.children.size() < count || control.operands.size() < count)
      return refuse(op.span, "control header coverage differs from source");
    for (unsigned i = 0; i < count; ++i) {
      auto expected = value(body, expr.children[i]);
      if (!expected || control.operands[i].index != expected->index)
        return types.diagnostic
                   ? false
                   : refuse(op.span,
                            "control header value differs from source");
    }
    return true;
  }
  bool snapshot(const Body &body, ValueId value, Span span, uint64_t before) {
    const auto &index = indices.at(&body);
    if (!types.charge(2 * sourceLevels + 1, span))
      return false;
    if (value.index >= index.origins.size())
      return refuse(span);
    const auto &origin = index.origins[value.index];
    if (!origin)
      return refuse(span, "capture has no lexical origin");
    auto versions = index.generations.find(origin->binding);
    if (versions == index.generations.end())
      return refuse(span, "capture has no source generation");
    auto end = versions->second.upper_bound(before);
    if (end == versions->second.begin() ||
        *std::prev(end) != origin->generation)
      return refuse(span,
                    "capture value differs from current source generation");
    return true;
  }
  bool initialState(const Body &body, ArrayRef<ValueId> carried,
                    uint32_t expression, Span span) {
    const auto &writes = stateWrites[expression];
    if (!types.charge(writes.size() + carried.size() + 1, span))
      return false;
    if (carried.size() != writes.size())
      return refuse(span, "loop initial state coverage differs from source");
    auto binding = writes.begin();
    const auto &origins = indices.at(&body).origins;
    for (auto operand : carried) {
      if (!snapshot(body, operand, span, events[expression].capture))
        return false;
      if (operand.index >= origins.size() || !origins[operand.index] ||
          !origins[operand.index]->path.empty() ||
          origins[operand.index]->binding != *binding++)
        return refuse(span, "loop initial state differs from source binding");
    }
    return true;
  }
  bool snapshots(const Body &body, const Operation &op,
                 ArrayRef<ValueId> operands) {
    if (!op.expression || !types.charge(sourceLevels, op.span))
      return types.diagnostic ? false : refuse(op.span);
    const auto expression = *op.expression;
    auto found = sourceInputs.find(expression);
    if (found == sourceInputs.end()) {
      const auto &expr = syntax.expressions[expression];
      FreePlaceEnvironment lexical;
      lexical.dataBinding = [&](BindingId id) {
        if (!types.charge(sourceLevels, expr.span))
          return false;
        const auto &binding = syntax.bindings[id.index];
        return !binding.service && !binding.scoped && !binding.domain &&
               binding.span.begin < expr.span.begin;
      };
      lexical.place = [&](uint32_t id)
          -> std::optional<std::pair<BindingId, std::vector<unsigned>>> {
        auto origin = place(id, 1);
        if (!origin)
          return {};
        return std::pair{BindingId{origin->binding}, std::move(origin->path)};
      };
      auto inputs = queryFreePlaces(types, syntax, expr, lexical);
      if (!inputs || types.diagnostic)
        return false;
      found = sourceInputs.emplace(expression, std::move(*inputs)).first;
    }
    const auto &expected = found->second;
    const SourceControlSnapshot empty;
    const auto *resolved = events[expression].snapshot;
    if (!resolved)
      resolved = &empty;
    if (!expected.writes.empty() && resolved == &empty)
      return refuse(op.span, "missing resolved source state inventory");
    ArrayRef<ValueId> recipes(resolved->recipes);
    if (operands.size() < recipes.size() ||
        !types.charge(recipes.size() + 1, op.span))
      return types.diagnostic
                 ? false
                 : refuse(op.span, "recipe snapshot coverage differs");
    // Recipe operands were evaluated when the descriptor was formed. They can
    // intentionally precede later assignments, or have no lexical place at all.
    // Relate their supplied suffix to the immutable resolved source references;
    // only ordinary state/captures require the current entry generation.
    const auto supplied = operands.take_back(recipes.size());
    for (unsigned i = 0; i < recipes.size(); ++i) {
      // Restrictions preserve each retained participant's eager value, but
      // must not broaden the identity relation used by returns/state yields.
      auto actual = recipeRoot(body, supplied[i], op);
      auto expected = recipeRoot(body, recipes[i], op);
      if (!actual || !expected)
        return false;
      if (actual->index != expected->index)
        return refuse(op.span, "recipe snapshot differs from resolved source");
      const auto *repeat = std::get_if<ProtocolRepeat>(&op.action);
      const auto &before = body.values[recipes[i].index];
      const auto &after = body.values[supplied[i].index];
      if (!repeat)
        return refuse(op.span, "recipe capture requires a protocol repeat");
      if (!types.chargeType(before.type, op.span) ||
          !types.chargeType(after.type, op.span) ||
          !types.charge(before.components.size() + after.components.size() +
                            repeat->roles.size() + 1,
                        op.span))
        return false;
      std::vector<unsigned> selected;
      std::set_intersection(before.components.begin(), before.components.end(),
                            repeat->roles.begin(), repeat->roles.end(),
                            std::back_inserter(selected));
      const auto *placed =
          after.placement ? std::get_if<DataPlacement>(&after.placement->value)
                          : nullptr;
      if (before.type != after.type || selected.empty() ||
          after.components != selected || after.oracleHolder ||
          (after.placement && (!placed || placed->roles != selected)))
        return refuse(op.span,
                      "recipe capture participants differ from source");
    }
    operands = operands.drop_back(recipes.size());
    if (!types.charge((operands.size() + expected.places.size() + 1) *
                          sourceLevels,
                      op.span))
      return false;
    const auto &origins = indices.at(&body).origins;
    for (auto operand : operands)
      if (!snapshot(body, operand, op.span, events[expression].capture))
        return false;
    unsigned next = 0;
    std::set<BindingId> states;
    if (!types.charge(resolved->initial.size() * sourceLevels, op.span))
      return false;
    // Availability is the frozen result of ordinary source usage resolution.
    // A consumed state can be absent, but the candidate cannot choose absence.
    for (auto binding : resolved->initial) {
      if (next == operands.size())
        return refuse(op.span, "incoming source state coverage differs");
      const auto &origin = *origins[operands[next++].index];
      if (!origin.path.empty() || origin.binding != binding.index ||
          !expected.writes.count(binding) ||
          (!states.empty() && !(*states.rbegin() < binding)))
        return refuse(op.span, "incoming source state differs");
      states.insert(binding);
    }
    for (const auto &place : expected.places) {
      if (states.count(place.binding))
        continue;
      if (next == operands.size())
        return refuse(op.span, "source snapshot coverage differs");
      const auto &origin = *origins[operands[next++].index];
      if (!types.charge(origin.path.size() + place.path.size() + 1, op.span))
        return false;
      if (origin.binding != place.binding.index || origin.path != place.path ||
          (origin.path.empty() && expected.writes.count(place.binding)))
        return refuse(op.span, "source snapshot place differs");
    }
    return next == operands.size() ||
           refuse(op.span, "source snapshot coverage differs");
  }
  bool state(const Body &body, ValueId actual, uint32_t expression,
             std::vector<Origin> &states, Span span) {
    const auto &index = indices.at(&body);
    if (!types.charge(2 * sourceLevels + 1, span))
      return false;
    if (actual.index >= index.origins.size() || !index.origins[actual.index])
      return refuse(span, "state yield has no lexical origin");
    const auto &origin = *index.origins[actual.index];
    if (!origin.path.empty() ||
        !stateWrites[expression].count(origin.binding) ||
        (!states.empty() && states.back().binding >= origin.binding) ||
        *index.generations.at(origin.binding).rbegin() != origin.generation)
      return refuse(span, "state yield differs from its latest source binding");
    states.push_back(origin);
    return true;
  }
  bool selection(const Body &body, const Operation &op,
                 const Control &control) {
    if (!wholeBody)
      return true;
    std::optional<std::vector<Origin>> joined;
    std::optional<Type> explicitType;
    const bool loop = control.kind == Control::Kind::For;
    if (loop) {
      auto result = value(body, *op.expression);
      if (!result || !unit(body, *result))
        return types.diagnostic
                   ? false
                   : refuse(op.span, "loop unit value differs from source");
    }
    for (const auto &region : control.regions) {
      const auto &arm = *region;
      if (arm.stopped)
        continue;
      auto expected = tail(arm);
      if (types.diagnostic || arm.results.empty())
        return types.diagnostic ? false
                                : refuse(op.span, "control yield is missing");
      const Type empty(Type::Kind::Unit);
      const Type &type = expected ? arm.values[expected->index].type : empty;
      if (!types.chargeType(type, op.span))
        return false;
      if (explicitType && !types.chargeType(*explicitType, op.span))
        return false;
      if (explicitType && *explicitType != type)
        return refuse(op.span, "control source tail types differ");
      explicitType = type;
      const auto actual = arm.results.front();
      if (actual.index >= arm.values.size() || op.results.size() != 1 ||
          op.results.front().index >= body.values.size())
        return refuse(op.span, "control result type differs from yield");
      if (!types.chargeType(arm.values[actual.index].type, op.span) ||
          !types.chargeType(body.values[op.results.front().index].type,
                            op.span))
        return false;
      if (arm.values[actual.index].type !=
          body.values[op.results.front().index].type)
        return refuse(op.span, "control result type differs from yield");
      std::vector<ValueId> fields;
      if (type.kind != Type::Kind::Unit) {
        if (!sameValue(arm, actual, *expected)) {
          auto *pack = aggregate(arm, actual);
          if (!pack || pack->operands.empty() ||
              !sameValue(arm, pack->operands.front(), *expected))
            return refuse(op.span, "control yield differs from source tail");
          if (!types.charge(pack->operands.size(), op.span))
            return false;
          fields.assign(pack->operands.begin() + 1, pack->operands.end());
        }
      } else {
        const auto &index = indices.at(&arm);
        if (index.origins[actual.index])
          fields.push_back(actual);
        else if (!unit(arm, actual)) {
          auto *pack = aggregate(arm, actual);
          if (!pack)
            return refuse(op.span, "control state pack differs from source");
          if (!types.charge(pack->operands.size(), op.span))
            return false;
          fields = pack->operands;
        }
      }
      if (!types.charge(2 * fields.size() + 1, op.span))
        return false;
      std::vector<Origin> states;
      for (auto field : fields)
        if (!state(arm, field, *op.expression, states, op.span))
          return false;
      if (joined) {
        if (joined->size() != states.size())
          return refuse(op.span, "joined source state coverage differs");
        for (unsigned i = 0; i < states.size(); ++i)
          if (!states[i].samePlace((*joined)[i]))
            return refuse(op.span, "joined source state order differs");
      } else
        joined = states;
      if (loop) {
        if (states.size() != control.carried ||
            control.operands.size() < 2 + control.carried ||
            arm.results.size() !=
                1 + control.operands.size() - 2 - control.carried)
          return refuse(op.span, "loop state coverage differs from source");
        const auto &parent = indices.at(&body);
        for (unsigned i = 0; i < states.size(); ++i) {
          const auto &incoming = parent.origins[control.operands[2 + i].index];
          if (!incoming || !states[i].samePlace(*incoming))
            return refuse(op.span,
                          "loop initial state differs from source binding");
        }
        unsigned invariants = control.operands.size() - 2 - control.carried;
        for (unsigned i = 0; i < invariants; ++i)
          if (!sameValue(arm, arm.results[1 + i],
                         ValueId{arm.inputs - invariants + i}))
            return refuse(op.span, "loop invariant yield differs from input");
      } else if (arm.results.size() != 1)
        return refuse(op.span, "control yield coverage differs from source");
    }
    if (joined) {
      ArrayRef<BindingId> expected;
      if (const auto *resolved = events[*op.expression].snapshot)
        expected = resolved->joined;
      if (!types.charge(expected.size() + joined->size() + 1, op.span))
        return false;
      bool matches = joined->size() == expected.size();
      if (matches)
        for (unsigned i = 0; i < expected.size(); ++i)
          matches &= (*joined)[i].binding == expected[i].index;
      // Preserve the more precise authored-read refusal when one exists. Even
      // an unused successor must match the resolved live state inventory.
      if (!matches)
        indices.at(&body).invalidStateJoin = op.span;
    }
    // All-stopped controls have no source value; SourceExits owns that outcome.
    if (!explicitType)
      return true;
    auto actual = value(body, *op.expression);
    if (!actual)
      return false;
    if (explicitType->kind == Type::Kind::Unit)
      return unit(body, *actual) ||
             refuse(op.span, "control unit value differs from source");
    if (joined && !joined->empty()) {
      const auto *producer = indices.at(&body).producers[actual->index];
      const auto *projection =
          producer ? std::get_if<Projection>(&producer->action) : nullptr;
      if (!projection || projection->path != std::vector<unsigned>{0} ||
          projection->input.index != op.results.front().index)
        return refuse(op.span, "control result projection differs from source");
      return true;
    }
    return sameValue(body, *actual, op.results.front()) ||
           refuse(op.span, "control result value differs from source");
  }
  bool repeat(const Body &body, const Operation &op,
              const ProtocolRepeat &repeat) {
    if (!wholeBody || !op.expression)
      return !wholeBody || refuse(op.span);
    const auto &expr = syntax.expressions[*op.expression];
    auto result = value(body, *op.expression);
    if (!result || !unit(body, *result))
      return types.diagnostic
                 ? false
                 : refuse(op.span, "repeat unit value differs from source");
    auto count = value(body, expr.children[1]);
    if (!count || count->index != repeat.count.index)
      return types.diagnostic
                 ? false
                 : refuse(op.span, "repeat count differs from source");
    if (!source.repeatMaxima || !source.repeatMaxima->count(*op.expression) ||
        repeat.maximum != source.repeatMaxima->at(*op.expression))
      return refuse(op.span, "repeat maximum differs from source");
    const auto &region = *repeat.region;
    if (region.stopped)
      return true;
    if (region.results.size() != repeat.carried.size())
      return refuse(op.span, "repeat state yield coverage differs");
    std::vector<Origin> states;
    const auto &parent = indices.at(&body);
    for (unsigned i = 0; i < repeat.carried.size(); ++i) {
      if (!state(region, region.results[i], *op.expression, states, op.span))
        return false;
      const auto &incoming = parent.origins[repeat.carried[i].index];
      if (!incoming || !states.back().samePlace(*incoming))
        return refuse(op.span,
                      "repeat initial state differs from source binding");
    }
    return true;
  }
  bool body(const Body &body, Origins inputs, unsigned depth,
            std::vector<OriginTree> *outputs = nullptr,
            std::optional<uint32_t> callback = {}, bool controlRegion = false) {
    const auto &expressionValues = body.expressionValues;
    if (!bounded(depth, {}) ||
        !types.charge(7 * body.values.size() + 2 * body.operations.size() +
                          expressionValues.size(),
                      {}))
      return false;
    if (inputs.size() != body.inputs)
      return refuse({});
    auto [entry, inserted] = indices.try_emplace(&body);
    if (!inserted)
      return refuse({}, "candidate body is shared by different source regions");
    auto &index = entry->second;
    index.origins = std::move(inputs);
    auto &origins = index.origins;
    origins.resize(body.values.size());
    if (wholeBody)
      if (auto inputs = inputBindings.find(&body);
          inputs != inputBindings.end())
        for (auto [slot, binding] : inputs->second)
          origins[slot] = Origin{binding.index, {}};
    index.producers.resize(body.values.size());
    index.identities.resize(body.values.size());
    index.recipeIdentities.resize(body.values.size());
    index.aggregates.resize(body.values.size());
    auto &producers = index.producers;
    std::vector<OriginTree> trees(body.values.size());
    for (unsigned i = 0; i < body.values.size(); ++i) {
      index.identities[i] = ValueId{i};
      index.recipeIdentities[i] = ValueId{i};
    }
    for (unsigned i = 0; i < body.inputs; ++i)
      if (origins[i]) {
        if (!chargeOrigin(origins[i], {}))
          return false;
        trees[i].emplace(std::vector<unsigned>{}, *origins[i]);
      }
    if (wholeBody)
      for (unsigned i = 0; i < body.inputs; ++i)
        if (origins[i])
          index.generations[origins[i]->binding].insert(origins[i]->generation);
    if (wholeBody) {
      const auto context = occurrences->candidates.at(&body);
      if (auto found = occurrences->bindings.find(context);
          found != occurrences->bindings.end())
        for (const auto &definition : found->second) {
          if (definition.parameter) {
            if (!types.charge(sourceLevels, definition.span))
              return false;
            index.generations[definition.binding.index].insert(0);
            continue;
          }
          if (!types.charge(3 * sourceLevels, definition.span))
            return false;
          auto event = definitionEvents.find(key(definition.span));
          if (event == definitionEvents.end())
            return refuse(definition.span, "missing authored definition event");
          index.generations[definition.binding.index].insert(event->second);
        }
      if (auto found = occurrences->controls.find(context);
          found != occurrences->controls.end())
        for (auto expression : found->second) {
          const auto &writes = stateWrites[expression];
          if (!types.charge((writes.size() + 1) * sourceLevels,
                            syntax.expressions[expression].span))
            return false;
          for (auto binding : writes)
            index.generations[binding].insert(events[expression].finish);
        }
    }
    std::set<const Operation *> checkedCalls, checkedQueries;
    uint32_t invocationEnd = 0;
    for (const auto &op : body.operations) {
      // Authenticated source spans are postorder coordinates: child calls
      // finish before their parent, and written arguments finish left to right.
      if (wholeBody && op.binding) {
        if (op.span.end < invocationEnd)
          return refuse(op.span,
                        "authored invocation evaluation order differs");
        invocationEnd = op.span.end;
      }
      if (std::holds_alternative<HelperCall>(op.action) && !op.binding)
        return refuse(op.span);
      for (auto value : op.results) {
        if (value.index < body.inputs || value.index >= producers.size() ||
            producers[value.index])
          return refuse(op.span);
        producers[value.index] = &op;
      }
      if (!carrier(body, op, index))
        return false;
      if (const auto *projection = std::get_if<Projection>(&op.action)) {
        if (projection->input.index >= origins.size() || op.results.size() != 1)
          return refuse(op.span);
        const auto &input = body.values[projection->input.index].type;
        if (!projection->path.empty() && input.kind != Type::Kind::Tuple &&
            input.kind != Type::Kind::Array &&
            input.kind != Type::Kind::Record &&
            input.kind != Type::Kind::LogicalRecord &&
            input.kind != Type::Kind::Associated)
          return refuse(op.span, "projection input is not a product");
        if (!types.chargeType(input, op.span) ||
            !types.chargeType(body.values[op.results.front().index].type,
                              op.span))
          return false;
        auto projected =
            types.projectedType(owner, input, projection->path, op.span);
        if (!projected ||
            *projected != body.values[op.results.front().index].type)
          return types.diagnostic
                     ? false
                     : refuse(op.span, "projection result type differs");
        if (!chargeOrigin(origins[projection->input.index], op.span))
          return false;
        auto origin = origins[projection->input.index];
        if (origin) {
          if (!types.charge(origin->path.size() + projection->path.size() + 1,
                            op.span))
            return false;
          origin->path.insert(origin->path.end(), projection->path.begin(),
                              projection->path.end());
        } else {
          for (const auto &[path, origin] : trees[projection->input.index]) {
            if (!types.charge(path.size() + origin.path.size() + 1, op.span))
              return false;
            if (projection->path.size() <= path.size() &&
                std::equal(projection->path.begin(), projection->path.end(),
                           path.begin()))
              trees[op.results.front().index].emplace(
                  std::vector<unsigned>(path.begin() + projection->path.size(),
                                        path.end()),
                  origin);
          }
        }
        origins[op.results.front().index] = std::move(origin);
        auto alias = aliases.find(key(op.span));
        if (!wholeBody && alias != aliases.end()) {
          auto expected = expressionValues.find(alias->second);
          if (expected != expressionValues.end() &&
              (!projection->path.empty() ||
               projection->input.index != expected->second.index))
            return refuse(op.span);
        }
        if (wholeBody && projection->path.empty()) {
          if (auto found = authenticatedBindings.find(&op);
              found != authenticatedBindings.end()) {
            const auto &definition = *found->second;
            if (!this->alias(body, op, definition, producers))
              return false;
            origins[op.results.front().index] =
                Origin{definition.binding.index,
                       {},
                       definition.parameter
                           ? 0
                           : definitionEvents.at(key(definition.span))};
          }
        }
      } else if (const auto *restriction =
                     std::get_if<Restriction>(&op.action)) {
        if (restriction->input.index >= origins.size() ||
            op.results.size() != 1)
          return refuse(op.span);
        if (!chargeOrigin(origins[restriction->input.index], op.span) ||
            !chargeTree(trees[restriction->input.index], op.span))
          return false;
        origins[op.results.front().index] = origins[restriction->input.index];
        trees[op.results.front().index] = trees[restriction->input.index];
      } else if (const auto *construct = std::get_if<Construct>(&op.action);
                 construct && construct->kind == Construct::Kind::Aggregate &&
                 op.results.size() == 1) {
        for (unsigned i = 0; i < construct->operands.size(); ++i) {
          auto operand = construct->operands[i];
          if (operand.index >= trees.size() ||
              (operand.index >= body.inputs &&
               (!producers[operand.index] || producers[operand.index] == &op)))
            return refuse(op.span, "aggregate operand is unavailable");
          for (const auto &[path, origin] : trees[operand.index]) {
            if (!types.charge(path.size() + origin.path.size() + 1, op.span))
              return false;
            std::vector<unsigned> nested{i};
            nested.insert(nested.end(), path.begin(), path.end());
            trees[op.results.front().index].emplace(std::move(nested), origin);
          }
        }
      }
      if (const auto *projection = std::get_if<Projection>(&op.action);
          projection && projection->path.empty() && !op.binding &&
          op.results.size() == 1 &&
          projection->input.index < body.values.size()) {
        const auto result = op.results.front();
        if (!types.chargeType(body.values[result.index].type, op.span))
          return false;
        if (body.values[projection->input.index].type ==
            body.values[result.index].type) {
          if (projection->input.index >= body.inputs &&
              (!producers[projection->input.index] ||
               producers[projection->input.index] == &op))
            return refuse(op.span, "identity value edge is not available");
          index.identities[result.index] =
              index.identities[projection->input.index];
          const auto &before = body.values[projection->input.index];
          const auto &after = body.values[result.index];
          const auto *beforePlacement =
              before.placement
                  ? std::get_if<DataPlacement>(&before.placement->value)
                  : nullptr;
          const auto *afterPlacement =
              after.placement
                  ? std::get_if<DataPlacement>(&after.placement->value)
                  : nullptr;
          if (!types.charge(
                  before.components.size() + after.components.size() +
                      (beforePlacement ? beforePlacement->roles.size() : 0) +
                      (afterPlacement ? afterPlacement->roles.size() : 0) + 1,
                  op.span))
            return false;
          // Validate once in producer order, then propagate the validated root
          // (or invalidity) without rescanning chains for each recipe capture.
          // Recipes retain ordinary data; reject other placement kinds without
          // walking an unrelated logical placement tree.
          const bool samePlacement =
              (!before.placement && !after.placement) ||
              (beforePlacement && afterPlacement &&
               beforePlacement->roles == before.components &&
               beforePlacement->roles == afterPlacement->roles);
          index.recipeIdentities[result.index] =
              before.components == after.components && !before.oracleHolder &&
                      !after.oracleHolder && samePlacement
                  ? index.recipeIdentities[projection->input.index]
                  : std::nullopt;
        }
      }
      if (const auto *control = std::get_if<LocalControl>(&op.action)) {
        if (wholeBody && !header(body, op, *control))
          return false;
        unsigned head = control->kind == LocalControl::Kind::For ? 2 : 1;
        if (control->operands.size() < head || op.results.size() != 1)
          return refuse(op.span);
        unsigned captured = control->operands.size() - head;
        if (wholeBody && control->kind == Control::Kind::For &&
            (control->carried > captured ||
             !initialState(body,
                           ArrayRef<ValueId>(control->operands)
                               .slice(2, control->carried),
                           *op.expression, op.span)))
          return types.diagnostic ? false : refuse(op.span);
        if (wholeBody &&
            !snapshots(body, op,
                       ArrayRef<ValueId>(control->operands).drop_front(head)))
          return false;
        std::optional<OriginTree> joined;
        std::optional<bool> explicitResult;
        bool packedResult = false;
        if (control->kind == LocalControl::Kind::For) {
          if (control->carried > captured)
            return refuse(op.span);
          joined.emplace();
          for (unsigned i = 0; i < control->carried; ++i) {
            auto operand = control->operands[head + i];
            if (operand.index >= trees.size())
              return refuse(op.span);
            for (const auto &[path, origin] : trees[operand.index]) {
              if (!types.charge(path.size() + origin.path.size() + 1, op.span))
                return false;
              auto selected = path;
              if (control->carried != 1)
                selected.insert(selected.begin(), i);
              joined->emplace(std::move(selected), origin);
            }
          }
        }
        for (const auto &region : control->regions) {
          if (region->inputs < captured)
            return refuse(op.span);
          if (!types.charge(region->inputs, op.span))
            return false;
          Origins nested(region->inputs);
          for (unsigned i = 0; i < captured; ++i) {
            auto operand = control->operands[head + i];
            if (operand.index >= origins.size())
              return refuse(op.span);
            if (!chargeOrigin(origins[operand.index], op.span))
              return false;
            nested[region->inputs - captured + i] = origins[operand.index];
          }
          std::vector<OriginTree> results;
          if (!this->body(*region, std::move(nested), depth + 1, &results,
                          callback, true))
            return false;
          if (region->stopped)
            continue;
          if (results.empty())
            return refuse(op.span);
          if (wholeBody && !explicitResult) {
            auto expected = tail(*region);
            if (types.diagnostic)
              return false;
            explicitResult =
                expected &&
                region->values[expected->index].type.kind != Type::Kind::Unit;
            packedResult =
                *explicitResult &&
                !sameValue(*region, region->results.front(), *expected);
          }
          if (!joined)
            joined = std::move(results.front());
          else
            for (auto at = joined->begin(); at != joined->end();) {
              auto other = results.front().find(at->first);
              if (!types.charge(at->first.size() + at->second.path.size() +
                                    (other == results.front().end()
                                         ? 0
                                         : other->second.path.size()) +
                                    1,
                                op.span))
                return false;
              if (other == results.front().end() ||
                  !other->second.samePlace(at->second))
                at = joined->erase(at);
              else {
                at->second.generation =
                    std::max(at->second.generation, other->second.generation);
                ++at;
              }
            }
        }
        if (joined) {
          if (!types.charge(joined->size() + 1, op.span))
            return false;
          for (auto &[path, origin] : *joined)
            if (wholeBody) {
              const bool statePath =
                  !explicitResult.value_or(false) ||
                  (packedResult && !path.empty() && path.front() != 0);
              if (statePath &&
                  stateWrites[*op.expression].count(origin.binding))
                origin.generation = events[*op.expression].finish;
            } else
              for (auto operand : llvm::drop_begin(control->operands, head)) {
                const auto &incoming = origins[operand.index];
                if (incoming && incoming->binding == origin.binding &&
                    origin.generation > incoming->generation) {
                  origin.generation = op.span.end;
                  break;
                }
              }
          trees[op.results.front().index] = std::move(*joined);
        }
      }
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        const auto &region = *repeat->region;
        if (wholeBody &&
            !initialState(body, repeat->carried, *op.expression, op.span))
          return false;
        if (wholeBody) {
          if (!types.charge(repeat->carried.size() + repeat->captures.size(),
                            op.span))
            return false;
          auto operands = repeat->carried;
          operands.insert(operands.end(), repeat->captures.begin(),
                          repeat->captures.end());
          if (!snapshots(body, op, operands))
            return false;
        }
        if (!types.charge(region.inputs, op.span))
          return false;
        Origins nested(region.inputs);
        if (nested.size() !=
                1 + repeat->carried.size() + repeat->captures.size() ||
            region.services.size() != repeat->services.size())
          return refuse(op.span);
        if (op.results.size() != repeat->carried.size())
          return refuse(op.span);
        for (unsigned i = 0; i < repeat->carried.size(); ++i) {
          auto operand = repeat->carried[i];
          if (operand.index >= trees.size())
            return refuse(op.span);
          if (!chargeTree(trees[operand.index], op.span))
            return false;
          trees[op.results[i].index] = trees[operand.index];
        }
        unsigned next = 1;
        for (auto list : {ArrayRef<ValueId>(repeat->carried),
                          ArrayRef<ValueId>(repeat->captures)})
          for (auto operand : list) {
            if (operand.index >= origins.size())
              return refuse(op.span);
            if (!chargeOrigin(origins[operand.index], op.span))
              return false;
            nested[next++] = origins[operand.index];
          }
        for (unsigned i = 0; i < repeat->services.size(); ++i) {
          auto root = repeat->services[i].index;
          if (root >= body.services.size() ||
              key(region.services[i].span) != key(body.services[root].span) ||
              region.services[i].field != body.services[root].field ||
              region.services[i].owner != body.services[root].owner)
            return refuse(op.span);
        }
        std::vector<OriginTree> results;
        if (!this->body(region, std::move(nested), depth + 1, &results,
                        callback, true))
          return false;
        if (!region.stopped && results.size() != op.results.size())
          return refuse(op.span);
        for (unsigned i = 0; i < results.size(); ++i) {
          const auto &incoming = origins[repeat->carried[i].index];
          for (auto &[path, origin] : results[i])
            if ((wholeBody &&
                 stateWrites[*op.expression].count(origin.binding)) ||
                (!wholeBody && incoming &&
                 incoming->binding == origin.binding &&
                 origin.generation > incoming->generation))
              origin.generation =
                  wholeBody ? events[*op.expression].finish : op.span.end;
          trees[op.results[i].index] = std::move(results[i]);
        }
      }
      for (auto result : op.results) {
        if (origins[result.index]) {
          if (!chargeOrigin(origins[result.index], op.span))
            return false;
          trees[result.index] = {{{}, *origins[result.index]}};
        } else if (auto root = trees[result.index].find({});
                   root != trees[result.index].end()) {
          if (!types.charge(root->second.path.size() + 1, op.span))
            return false;
          origins[result.index] = root->second;
        }
      }
    }
    auto &generations = index.generations;
    if (wholeBody) {
      const auto context = occurrences->candidates.at(&body);
      if (auto required = occurrences->values.find(context);
          required != occurrences->values.end())
        for (auto id : required->second)
          if (!this->value(body, id))
            return false;
      for (const auto &op : body.operations) {
        if (const auto *control = std::get_if<Control>(&op.action))
          if (!selection(body, op, *control))
            return false;
        if (const auto *repeated = std::get_if<ProtocolRepeat>(&op.action))
          if (!repeat(body, op, *repeated))
            return false;
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
        if (wholeBody) {
          const auto &versions = generations[expected->binding];
          auto after = versions.upper_bound(events[id].read);
          if (after == versions.begin())
            return refuse(expr.span);
          expected->generation = *std::prev(after);
        }
        if (origins[actual.index] != expected)
          return refuse(expr.span, "lexical value origin differs");
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
      bool transparent = expr.kind == Expression::Kind::Block;
      if (transparent) {
        if (expr.regions.size() != 1 ||
            expr.regions.front() >= syntax.bodies.size())
          return refuse(expr.span);
        const auto &region = syntax.bodies[expr.regions.front()];
        if (region.results.size() == 1) {
          auto result = value(region.results.front().second);
          if (!result || result->index != actual.index)
            return refuse(expr.span,
                          "block value differs from its source tail");
        } else {
          const auto *unit = op ? std::get_if<Construct>(&op->action) : nullptr;
          if (!region.results.empty() || !unit ||
              unit->kind != Construct::Kind::Aggregate ||
              !unit->operands.empty() ||
              body.values[actual.index].type.kind != Type::Kind::Unit ||
              key(op->span) != key(region.span))
            return refuse(expr.span, "block unit differs from its source tail");
        }
      }
      if (expr.kind == Expression::Kind::OracleContents &&
          owner.oraclePredicateOwner) {
        if (expr.children.size() != 1 || !value(expr.children.front()) ||
            value(expr.children.front())->index != actual.index)
          return refuse(expr.span);
        transparent = true;
      }
      if (wholeBody && !place(id, depth) && !transparent &&
          (!op || key(op->span) != key(expr.span)))
        return refuse(expr.span, "expression producer occurrence differs");
      // The immutable authored occurrence chooses its required producer. A
      // candidate action or originating-expression hint cannot opt out of it.
      const bool selected = expr.kind == Expression::Kind::And ||
                            expr.kind == Expression::Kind::Or;
      const bool variant = source.enumTypes && source.enumTypes->count(id);
      const bool decimal = expr.kind == Expression::Kind::Decimal &&
                           source.literals && source.literals->count(id);
      const bool literal = expr.kind == Expression::Kind::Boolean || decimal;
      const bool query = expr.kind == Expression::Kind::OracleQuery;
      if (!op || key(op->span) != key(expr.span)) {
        if (selected || variant || literal || query)
          return refuse(expr.span, "authored expression producer is missing");
        continue;
      }
      if (selected || variant || literal || query) {
        auto result = actual;
        // Local selection also returns updated mutable bindings in a tuple;
        // the authored Boolean is its first component.
        if (selected && body.mode == Body::Mode::Local) {
          if (const auto *projection = std::get_if<Projection>(&op->action);
              projection && projection->path == std::vector<unsigned>{0}) {
            result = projection->input;
            if (result.index >= producers.size())
              return refuse(expr.span);
            op = producers[result.index];
          }
        }
        // Short-circuit syntax also retains synthesized literal arms. Their
        // producers need not carry an originating-expression hint; the frozen
        // literal, exact span and mapped result authenticate them directly.
        if (!op || (!literal && !query && op->expression != id) ||
            op->binding || key(op->span) != key(expr.span) ||
            op->results.size() != 1 ||
            op->results.front().index != result.index)
          return refuse(expr.span, "authored expression producer differs");
      }
      if (query) {
        if (expr.children.size() != 2)
          return refuse(expr.span, "authored query arguments differ");
        auto handle = value(expr.children.front());
        auto position = value(expr.children.back());
        if (!handle || !position)
          return refuse(expr.span, "authored query operand is missing");
        if (const auto *sourceQuery =
                std::get_if<OracleSourceQuery>(&op->action)) {
          if (body.mode != Body::Mode::Oracle || !owner.oracleDefinition ||
              sourceQuery->source >= owner.oracleDefinition->sourceCount ||
              sourceQuery->position.index != position->index)
            return refuse(expr.span, "source query operands differ");
          // Oracle definitions record a constructor input index. Recover it
          // from the exact authored handle through typed identity aliases;
          // equal handle types do not establish source identity.
          auto root = *handle;
          unsigned steps = 0;
          while (root.index >= body.inputs) {
            if (!types.charge(1, expr.span))
              return false;
            if (++steps > body.operations.size() ||
                root.index >= producers.size())
              return refuse(expr.span, "invalid source query alias chain");
            const auto *producer = producers[root.index];
            const auto *alias =
                producer ? std::get_if<Projection>(&producer->action) : nullptr;
            if (!alias || !alias->path.empty() ||
                producer->results.size() != 1 ||
                producer->results.front().index != root.index ||
                alias->input.index >= body.values.size())
              return refuse(expr.span, "source query alias differs");
            const auto &inputType = body.values[alias->input.index].type;
            const auto &resultType = body.values[root.index].type;
            if (!types.chargeType(inputType, expr.span) ||
                !types.chargeType(resultType, expr.span))
              return false;
            if (inputType != resultType)
              return refuse(expr.span, "source query alias differs");
            root = alias->input;
          }
          if (root.index != sourceQuery->source)
            return refuse(expr.span, "source query selects a different input");
        } else {
          const auto *selectedQuery = std::get_if<OracleQuery>(&op->action);
          if (body.mode != Body::Mode::Protocol || !selectedQuery ||
              selectedQuery->handle.index != handle->index ||
              selectedQuery->position.index != position->index)
            return refuse(expr.span, "query operands differ from source");
        }
        if (!observedProducers.insert(id).second ||
            !checkedQueries.insert(op).second)
          return refuse(expr.span, "duplicate authored query occurrence");
        continue;
      }
      if (selected) {
        if (body.mode == Body::Mode::Protocol) {
          const auto *invoke = std::get_if<ScopedInvoke>(&op->action);
          if (!invoke || !invoke->operands.empty())
            return refuse(expr.span, "Boolean scoped producer differs");
        } else {
          const auto *control = std::get_if<Control>(&op->action);
          if (!control)
            return types.diagnostic
                       ? false
                       : refuse(expr.span, "Boolean selected producer differs");
        }
        observedProducers.insert(id);
        continue;
      }
      if (variant) {
        const auto *construct = std::get_if<Construct>(&op->action);
        if (!construct || construct->kind != Construct::Kind::Variant)
          return refuse(expr.span, "enum constructor producer differs");
        auto [nominal, alternative] = StringRef(expr.text).rsplit("::");
        if (expr.kind != Expression::Kind::Call || expr.binding ||
            alternative.empty() || construct->alternative != alternative ||
            !arguments(construct->operands, expr))
          return types.diagnostic ? false : refuse(expr.span);
        auto selected = storage.declarationIndex->lookup(
            SourceAccess{owner.id}, nominal,
            {[&] { return types.charge(1, expr.span); }, {}});
        const auto *reference = std::get_if<ResolvedReference>(&selected);
        const auto &type = body.values[actual.index].type;
        const auto *declaration = types.typeDeclaration(type);
        if (type != source.enumTypes->at(id) || !reference || !declaration ||
            declaration->kind != Declaration::Kind::Variant ||
            declaration->id.index != reference->target.index ||
            ((declaration->sealed || declaration->resource) &&
             !types.constructorAllowed(owner, type)) ||
            ((body.mode == Body::Mode::Math ||
              body.mode == Body::Mode::Protocol) &&
             !types.mathematicalData(type, expr.span, &owner)))
          return types.diagnostic ? false : refuse(expr.span);
        auto alternatives = types.alternatives(type, expr.span);
        if (!alternatives)
          return false;
        auto at = llvm::find_if(
            *alternatives, [alternative = alternative](const auto &candidate) {
              return candidate.name == alternative;
            });
        if (at == alternatives->end() ||
            at->fields.size() != construct->operands.size())
          return refuse(expr.span);
        for (unsigned i = 0; i < construct->operands.size(); ++i)
          if (body.values[construct->operands[i].index].type !=
              at->fields[i].type)
            return refuse(expr.span);
        observedProducers.insert(id);
        continue;
      }
      if (literal) {
        const Type boolean;
        const auto &type = decimal ? source.literals->at(id).first : boolean;
        const auto &payload =
            decimal ? source.literals->at(id).second : expr.text;
        if (!types.chargeType(type, expr.span) ||
            !types.chargeType(body.values[actual.index].type, expr.span) ||
            !types.charge(payload.size() + 1, expr.span))
          return false;
        if (body.values[actual.index].type != type)
          return refuse(expr.span, "literal type differs from source");
        const bool index = type.kind == Type::Kind::Index;
        if (body.mode == Body::Mode::Local) {
          const auto *constant = std::get_if<LocalPrimitive>(&op->action);
          const StringRef contract = !decimal ? "bool.constant"
                                     : index  ? "index.constant"
                                              : "field.constant";
          if (!constant ||
              !types.charge(constant->contract.size() + 1, expr.span))
            return types.diagnostic ? false : refuse(expr.span);
          if (constant->contract != contract ||
              constant->parameters.size() != 1 || !constant->operands.empty() ||
              constant->origin != LocalPrimitive::Origin::Primitive ||
              !constant->staticArguments.empty() ||
              constant->bindingArguments || !constant->assetReferences.empty())
            return refuse(expr.span, "literal differs from source");
          if (!types.charge(constant->parameters.front().size() + 1, expr.span))
            return false;
          if (constant->parameters.front() != payload)
            return refuse(expr.span, "literal differs from source");
        } else {
          const auto *constant = std::get_if<MathValue>(&op->action);
          const auto identity = !decimal ? MathematicalIdentity::BooleanConstant
                                : index  ? MathematicalIdentity::IndexConstant
                                         : MathematicalIdentity::FieldConstant;
          if (!constant ||
              !types.charge(constant->literal.size() + 1, expr.span))
            return types.diagnostic ? false : refuse(expr.span);
          if (constant->identity != identity || constant->literal != payload ||
              !constant->operands.empty() ||
              !constant->staticArguments.empty() ||
              !constant->parameters.empty())
            return refuse(expr.span, "literal differs from source");
        }
        observedProducers.insert(id);
      }
      if (op->binding) {
        checkedCalls.insert(op);
        const auto &binding = *op->binding;
        if (binding.target.declaration.index >= storage.declarations.size())
          return refuse(expr.span);
        if (binding.target.reference.category ==
            ResolutionCategory::ServiceMethod) {
          if (!checkCallAction(types, storage.declarations, body, *op,
                               storage.declarationIndex.get()))
            return false;
          continue;
        }
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
                        : callee.descriptorInputs[slot.index].name;
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
        if (!checkCallAction(types, storage.declarations, body, *op,
                             storage.declarationIndex.get()))
          return false;
        if (expr.kind == Expression::Kind::NotationCall ||
            expr.kind == Expression::Kind::Subscript || binding.notation) {
          if (!expr.notation || !binding.notation || !source.notationFamilies ||
              !source.notationFamilies->count(id) ||
              !source.notationFamilies->at(id) || !expr.scope ||
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
                    *source.notationFamilies->at(id), *expr.notation, binding,
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
        if (construct->kind == Construct::Kind::Variant)
          return refuse(expr.span,
                        "enum constructor has no authored occurrence");
        if ((expr.kind == Expression::Kind::Tuple ||
             expr.kind == Expression::Kind::Array) &&
            !arguments(construct->operands, expr))
          return false;
      }
    }
    if (index.invalidStateJoin)
      return refuse(*index.invalidStateJoin,
                    "joined live state coverage differs from source");
    for (const auto &op : body.operations) {
      if ((std::holds_alternative<OracleQuery>(op.action) ||
           std::holds_alternative<OracleSourceQuery>(op.action)) &&
          !checkedQueries.count(&op))
        return refuse(op.span, "query has no authored occurrence");
      if (op.binding && !checkedCalls.count(&op) &&
          !(wholeBody &&
            (op.binding->scopedSource || op.binding->intrinsicSource)))
        return refuse(op.span);
    }
    for (const auto &binding : body.scopedBindings) {
      if (!binding.computation)
        continue;
      const auto &computation = *binding.computation;
      if (!types.charge(computation.body->inputs, binding.span))
        return false;
      Origins nested(computation.body->inputs);
      unsigned explicitInputs = computation.signature.inputs.size();
      if (nested.size() != explicitInputs + binding.captures.size())
        return refuse(binding.span);
      for (unsigned i = 0; i < binding.captures.size(); ++i) {
        auto capture = binding.captures[i];
        if (capture.index >= origins.size())
          return refuse(binding.span);
        if (wholeBody && !snapshot(body, capture, binding.span,
                                   events[computation.expression].capture))
          return false;
        if (!chargeOrigin(origins[capture.index], binding.span))
          return false;
        nested[explicitInputs + i] = origins[capture.index];
      }
      if (!this->body(*computation.body, std::move(nested), depth + 1, nullptr,
                      computation.expression))
        return false;
    }
    if (!controlRegion && !returns(body, callback))
      return false;
    if (outputs)
      for (auto result : body.results) {
        if (result.index >= trees.size())
          return refuse({});
        if (!chargeTree(trees[result.index], {}))
          return false;
        outputs->push_back(trees[result.index]);
      }
    return true;
  }

public:
  ValueCheck(Semantics &types, const CheckedStorage &storage,
             const ScopedSource &source)
      : types(types), storage(storage), source(source), syntax(*source.syntax),
        owner(storage.declarations[source.owner.index]) {
    for (const auto &[binding, place] : source.environment)
      environment.emplace(binding, place.type);
  }
  bool run(const Body &checked, const SourceOccurrences &inventory) {
    wholeBody = true;
    occurrences = &inventory;
    if (!types.charge(syntax.expressions.size() + syntax.bindings.size() + 1,
                      owner.span))
      return false;
    if (syntax.bodies.empty())
      return true;
    bool query = owner.kind == Declaration::Kind::Oracle;
    if (checked.inputs != owner.inputs.size() + unsigned(query) ||
        syntax.inputBindings.size() != owner.inputs.size() ||
        checked.services.size() != syntax.services.size())
      return refuse(owner.span);
    Origins inputs(checked.inputs);
    for (unsigned i = 0; i < owner.inputs.size(); ++i) {
      inputs[i] = Origin{syntax.inputBindings[i].index, {}};
      environment.emplace(syntax.inputBindings[i], owner.inputs[i].type);
    }
    if (query) {
      if (!syntax.oracleDefinition || !syntax.oracleDefinition->queryBinding ||
          !owner.oracleDefinition)
        return refuse(owner.span);
      auto binding = *syntax.oracleDefinition->queryBinding;
      inputs.back() = Origin{binding.index, {}};
      environment.emplace(binding, owner.oracleDefinition->queryParameter.type);
    }
    for (unsigned i = 0; i < checked.services.size(); ++i)
      if (key(checked.services[i].span) != key(syntax.services[i].span))
        return refuse(owner.span);
    // Authenticate every reachable binding representation before importing any
    // proposed local type. A missing candidate cannot erase a Name obligation.
    if (!prepare(checked, 1))
      return false;
    for (auto [binding, type] : proposedTypes) {
      if (!types.chargeType(*type, owner.span))
        return false;
      auto [found, inserted] = environment.emplace(binding, *type);
      if (!inserted && found->second != *type)
        return refuse(owner.span, "binding generations have different types");
    }
    for (auto size = syntax.expressions.size() + syntax.bindings.size();
         size > 1; size >>= 1)
      ++sourceLevels;
    if (!types.charge(2 * syntax.expressions.size(), owner.span))
      return false;
    events.resize(syntax.expressions.size());
    if (source.controlSnapshots)
      for (const auto &[expression, snapshot] : *source.controlSnapshots) {
        if (!types.charge(1, owner.span))
          return false;
        if (expression >= events.size())
          return refuse(owner.span, "resolved state inventory has no source");
        events[expression].snapshot = &snapshot;
      }
    for (const auto &statement : syntax.bodies.front().statements) {
      if (!collect(statement.expression, 1))
        return false;
      const auto event = ++nextEvent;
      if (!types.charge(sourceLevels, statement.span) ||
          !definition(statement.pattern, event, 1))
        return false;
      definitionEvents.emplace(key(statement.span), event);
    }
    for (const auto &[name, result] : syntax.bodies.front().results)
      if (!collect(result, 1))
        return false;
    return body(checked, std::move(inputs), 1) &&
           ((observedReads == expectedReads &&
             observedNotations == expectedNotations &&
             observedProducers == expectedProducers) ||
            refuse(owner.span, "authored value occurrence coverage differs"));
  }
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
    const bool selected = authored.kind == Expression::Kind::And ||
                          authored.kind == Expression::Kind::Or;
    const auto &region = syntax.bodies.at(authored.regions.front());
    const auto &checked = *computation.body;
    if (selected) {
      auto result = checked.expressionValues.find(source.expression);
      if (checked.stopped || checked.results.size() != 1 ||
          result == checked.expressionValues.end() ||
          checked.results.front().index != result->second.index)
        return refuse(binding.span);
    } else if (!checked.stopped && !region.results.empty()) {
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
             observedNotations == expectedNotations &&
             observedProducers == expectedProducers) ||
            refuse(binding.span));
  }
};
} // namespace
bool checkScopedValues(Semantics &types, const CheckedStorage &storage,
                       const ScopedSource &source,
                       const ScopedBinding &binding) {
  return ValueCheck(types, storage, source).run(binding);
}
bool checkInvocationValues(Semantics &types, const CheckedStorage &storage,
                           const ScopedSource &source, const Body &body,
                           const SourceOccurrences &occurrences) {
  return ValueCheck(types, storage, source).run(body, occurrences);
}
} // namespace zkc::language::detail
