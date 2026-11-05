#include "BindingWitness.h"
#include "ScopedWitness.h"
#include "llvm/ADT/StringMap.h"
#include <algorithm>
#include <tuple>
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct Origin {
  uint32_t binding;
  std::vector<unsigned> path;
  uint32_t generation = 0;
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
  struct Alias {
    BindingId binding;
    std::optional<uint32_t> expression;
    std::optional<unsigned> parameter;
    std::vector<std::string> path;
    std::optional<Span> exchange = {};
  };
  // Desugared predicate and term parameters share their written binder spans.
  // The immutable lambda occurrence distinguishes their lexical definitions.
  using DefinitionKey = std::pair<std::optional<uint32_t>, SpanKey>;
  std::map<DefinitionKey, Alias> definitions;
  std::map<SpanKey, BindingId> lexicalInputs;
  std::set<uint32_t> expectedReads, observedReads;
  std::set<uint32_t> expectedNotations, observedNotations;
  std::set<uint32_t> expectedQueries, observedQueries;
  std::map<SpanKey, uint32_t> aliases;
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
        // Candidate spans may recover types, but must not decide whether an
        // authored data binding contributes a source-read obligation.
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
  const Alias *definition(Span span, std::optional<uint32_t> callback) const {
    auto found = definitions.find({callback, key(span)});
    if (found == definitions.end() && callback)
      found = definitions.find({{}, key(span)});
    return found == definitions.end() ? nullptr : &found->second;
  }
  bool pattern(const Pattern &pattern, Alias alias, unsigned depth,
               std::optional<uint32_t> callback = {}) {
    if (!bounded(depth, pattern.span))
      return false;
    if (pattern.kind == Pattern::Kind::Name && pattern.binding) {
      alias.binding = *pattern.binding;
      definitions.emplace(DefinitionKey{callback, key(pattern.span)},
                          std::move(alias));
    }
    for (unsigned i = 0; i < pattern.children.size(); ++i) {
      auto child = alias;
      child.path.push_back(pattern.kind == Pattern::Kind::Record
                               ? pattern.labels[i]
                               : std::to_string(i));
      if (!this->pattern(pattern.children[i], std::move(child), depth + 1,
                         callback))
        return false;
    }
    return true;
  }
  bool prepare(const Body &body, unsigned depth,
               std::optional<uint32_t> callback = {}) {
    if (!bounded(depth, {}) || !types.charge(body.values.size(), {}))
      return false;
    for (const auto &value : body.values) {
      if (const auto *at = definition(value.span, callback))
        environment.try_emplace(at->binding, value.type);
      auto input = lexicalInputs.find(key(value.span));
      if (input != lexicalInputs.end())
        environment.try_emplace(input->second, value.type);
    }
    for (const auto &op : body.operations) {
      if (const auto *control = std::get_if<LocalControl>(&op.action))
        for (const auto &region : control->regions)
          if (!prepare(*region, depth + 1, callback))
            return false;
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        if (!prepare(*repeat->region, depth + 1, callback))
          return false;
    }
    for (const auto &binding : body.scopedBindings)
      if (binding.computation && !prepare(*binding.computation->body, depth + 1,
                                          binding.computation->expression))
        return false;
    return true;
  }
  bool alias(const Body &body, const Operation &operation,
             const Alias &definition, ArrayRef<const Operation *> producers) {
    std::optional<ValueId> root;
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
  bool collect(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions.at(id);
    if (!bounded(depth, expr.span))
      return false;
    if (expr.kind == Expression::Kind::OracleQuery)
      expectedQueries.insert(id);
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
  bool body(const Body &body, Origins origins, unsigned depth,
            std::vector<OriginTree> *outputs = nullptr,
            std::optional<uint32_t> callback = {}) {
    const auto &expressionValues = body.expressionValues;
    if (!bounded(depth, {}) ||
        !types.charge(body.values.size() + body.operations.size() +
                          expressionValues.size(),
                      {}))
      return false;
    if (origins.size() != body.inputs)
      return refuse({});
    origins.resize(body.values.size());
    if (wholeBody)
      for (unsigned i = 0; i < body.inputs; ++i)
        if (!origins[i]) {
          auto input = lexicalInputs.find(key(body.values[i].span));
          if (input != lexicalInputs.end())
            origins[i] = Origin{input->second.index, {}};
        }
    std::vector<const Operation *> producers(body.values.size());
    std::vector<OriginTree> trees(body.values.size());
    for (unsigned i = 0; i < body.inputs; ++i)
      if (origins[i])
        trees[i].emplace(std::vector<unsigned>{}, *origins[i]);
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
        } else {
          for (const auto &[path, origin] : trees[projection->input.index]) {
            if (!types.charge(path.size() + 1, op.span))
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
          if (const auto *at = definition(op.span, callback)) {
            if (!this->alias(body, op, *at, producers))
              return false;
            origins[op.results.front().index] =
                Origin{at->binding.index, {}, op.span.end};
          }
        }
      } else if (const auto *restriction =
                     std::get_if<Restriction>(&op.action)) {
        if (restriction->input.index >= origins.size() ||
            op.results.size() != 1)
          return refuse(op.span);
        origins[op.results.front().index] = origins[restriction->input.index];
        trees[op.results.front().index] = trees[restriction->input.index];
      } else if (const auto *construct = std::get_if<Construct>(&op.action);
                 construct && construct->kind == Construct::Kind::Aggregate &&
                 op.results.size() == 1) {
        for (unsigned i = 0; i < construct->operands.size(); ++i) {
          auto operand = construct->operands[i];
          if (operand.index >= trees.size())
            return refuse(op.span);
          for (const auto &[path, origin] : trees[operand.index]) {
            if (!types.charge(path.size() + 1, op.span))
              return false;
            std::vector<unsigned> nested{i};
            nested.insert(nested.end(), path.begin(), path.end());
            trees[op.results.front().index].emplace(std::move(nested), origin);
          }
        }
      }
      if (const auto *control = std::get_if<LocalControl>(&op.action)) {
        unsigned head = control->kind == LocalControl::Kind::For ? 2 : 1;
        if (control->operands.size() < head || op.results.size() != 1)
          return refuse(op.span);
        unsigned captured = control->operands.size() - head;
        std::optional<OriginTree> joined;
        if (control->kind == LocalControl::Kind::For) {
          if (control->carried > captured)
            return refuse(op.span);
          joined.emplace();
          for (unsigned i = 0; i < control->carried; ++i) {
            auto operand = control->operands[head + i];
            if (operand.index >= trees.size())
              return refuse(op.span);
            for (const auto &[path, origin] : trees[operand.index]) {
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
          Origins nested(region->inputs);
          for (unsigned i = 0; i < captured; ++i) {
            auto operand = control->operands[head + i];
            if (operand.index >= origins.size())
              return refuse(op.span);
            nested[region->inputs - captured + i] = origins[operand.index];
          }
          std::vector<OriginTree> results;
          if (!this->body(*region, std::move(nested), depth + 1, &results,
                          callback))
            return false;
          if (region->stopped)
            continue;
          if (results.empty())
            return refuse(op.span);
          if (!joined)
            joined = std::move(results.front());
          else
            for (auto at = joined->begin(); at != joined->end();) {
              auto other = results.front().find(at->first);
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
          for (auto &[path, origin] : *joined)
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
          trees[op.results[i].index] = trees[operand.index];
        }
        unsigned next = 1;
        for (auto list : {ArrayRef<ValueId>(repeat->carried),
                          ArrayRef<ValueId>(repeat->captures)})
          for (auto operand : list) {
            if (operand.index >= origins.size())
              return refuse(op.span);
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
                        callback))
          return false;
        if (!region.stopped && results.size() != op.results.size())
          return refuse(op.span);
        for (unsigned i = 0; i < results.size(); ++i) {
          const auto &incoming = origins[repeat->carried[i].index];
          for (auto &[path, origin] : results[i])
            if (incoming && incoming->binding == origin.binding &&
                origin.generation > incoming->generation)
              origin.generation = op.span.end;
          trees[op.results[i].index] = std::move(results[i]);
        }
      }
      for (auto result : op.results) {
        if (origins[result.index])
          trees[result.index] = {{{}, *origins[result.index]}};
        else if (auto root = trees[result.index].find({});
                 root != trees[result.index].end())
          origins[result.index] = root->second;
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
    std::map<uint32_t, std::set<uint32_t>> generations;
    if (wholeBody)
      for (const auto &origin : origins)
        if (origin)
          generations[origin->binding].insert(origin->generation);
    for (const auto &[id, actual] : expressionValues) {
      if (id >= syntax.expressions.size() || actual.index >= origins.size())
        return refuse({});
      const auto &expr = syntax.expressions[id];
      if (!bounded(depth, expr.span))
        return false;
      if (auto expected = place(id, depth)) {
        if (wholeBody) {
          const auto &versions = generations[expected->binding];
          auto after = versions.upper_bound(expr.span.begin);
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
      if (expr.kind == Expression::Kind::OracleQuery) {
        if (!op || op->binding || key(op->span) != key(expr.span) ||
            op->results.size() != 1 ||
            op->results.front().index != actual.index ||
            expr.children.size() != 2)
          return refuse(expr.span, "authored query producer differs");
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
          // Constructor input identity follows the authored handle through
          // typed identity aliases, independently of the candidate source slot.
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
        if (!observedQueries.insert(id).second ||
            !checkedQueries.insert(op).second)
          return refuse(expr.span, "duplicate authored query occurrence");
        continue;
      }
      if (!op || key(op->span) != key(expr.span))
        continue;
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
        if (!checkCallAction(types, storage.declarations, body, *op,
                             storage.declarationIndex.get()))
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
             expr.kind == Expression::Kind::Array) &&
            !arguments(construct->operands, expr))
          return false;
      }
    }
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
      if (!this->body(*computation.body, std::move(nested), depth + 1, nullptr,
                      computation.expression))
        return false;
    }
    if (outputs)
      for (auto result : body.results) {
        if (result.index >= trees.size())
          return refuse({});
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
  bool run(const Body &checked) {
    wholeBody = true;
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
    for (const auto &region : syntax.bodies)
      for (const auto &statement : region.statements) {
        Alias definition{{0}, statement.expression, {}, {}};
        if (statement.exchange)
          definition.exchange = statement.span;
        if (statement.kind == Statement::Kind::Let &&
            !pattern(statement.pattern, definition, 1))
          return false;
        if (statement.kind == Statement::Kind::Assign &&
            statement.pattern.binding) {
          definition.binding = *statement.pattern.binding;
          definitions.emplace(DefinitionKey{{}, key(statement.span)},
                              std::move(definition));
        }
      }
    for (const auto &[id, expr] : llvm::enumerate(syntax.expressions)) {
      if (expr.index.binding)
        lexicalInputs.emplace(key(expr.index.span), *expr.index.binding);
      for (const auto &payload : expr.payloads)
        for (unsigned i = 0; i < payload.size(); ++i)
          if (!pattern(payload[i], Alias{{0}, {}, i, {}}, 1,
                       expr.kind == Expression::Kind::Lambda
                           ? std::optional<uint32_t>(id)
                           : std::nullopt))
            return false;
    }
    if (!prepare(checked, 1))
      return false;
    for (const auto &statement : syntax.bodies.front().statements)
      if (!collect(statement.expression, 1))
        return false;
    for (const auto &[name, result] : syntax.bodies.front().results)
      if (!collect(result, 1))
        return false;
    if (!body(checked, std::move(inputs), 1))
      return false;
    if (!checked.stopped) {
      const auto &written = syntax.bodies.front();
      if (!types.charge(owner.outputs.size() + written.results.size() + 1,
                        written.span))
        return false;
      llvm::StringMap<unsigned> outputs;
      if (query)
        outputs.try_emplace("result", 0);
      else
        for (unsigned i = 0; i < owner.outputs.size(); ++i) {
          if (!types.charge(owner.outputs[i].name.size() + 1, written.span))
            return false;
          outputs.try_emplace(owner.outputs[i].name, i);
        }
      if (checked.results.size() != outputs.size() ||
          written.results.size() != outputs.size())
        return refuse(written.span, "authored return coverage differs");
      std::set<unsigned> seen;
      for (const auto &[name, expression] : written.results) {
        if (!types.charge(name.size() + 1, written.span))
          return false;
        auto output = name.empty() && outputs.size() == 1 ? outputs.begin()
                                                          : outputs.find(name);
        auto value = checked.expressionValues.find(expression);
        if (output == outputs.end() || !seen.insert(output->second).second ||
            value == checked.expressionValues.end() ||
            checked.results[output->second].index != value->second.index)
          return refuse(written.span, "return differs from its authored value");
      }
    }
    return ((observedReads == expectedReads &&
             observedNotations == expectedNotations &&
             observedQueries == expectedQueries) ||
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
             observedNotations == expectedNotations &&
             observedQueries == expectedQueries) ||
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
                           const ScopedSource &source, const Body &body) {
  return ValueCheck(types, storage, source).run(body);
}
} // namespace zkc::language::detail
