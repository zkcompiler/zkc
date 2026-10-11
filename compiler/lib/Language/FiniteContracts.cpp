#include "FiniteContracts.h"
#include "DataRequirements.h"
#include "FiniteCardinality.h"
#include "FiniteFormation.h"
#include "MathematicalFacts.h"
#include "llvm/ADT/ScopeExit.h"
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct Item {
  unsigned domain;
  std::vector<unsigned> path;
};
using Facts = std::vector<std::optional<Item>>;
using OriginMap = std::map<unsigned, unsigned>;
using Restrictions = std::vector<OriginMap>;
using InputValues = std::vector<std::optional<ValueOrigin>>;
struct ItemBound {
  std::vector<unsigned> path;
  ValueOrigin container;
  unsigned axis;
};
using DataFact = SourceDataFact;

// A generic declaration is checked with distinct abstract domain identities.
// Literal bodies are checked at their binding occurrence, after all eager
// arguments have been elaborated. This makes named argument order irrelevant
// to checking without changing when captures or ordinary values are evaluated.
class ContractCheck {
  Semantics &types;
  MathematicalFacts mathematical;
  ArrayRef<Declaration> declarations;
  unsigned nextValue = 0;
  std::vector<std::vector<ItemBound>> domainBounds;
  struct DomainEvidence {
    facts::DomainNode node;
    std::vector<unsigned> children;
  };
  std::vector<DomainEvidence> domainEvidence;
  std::vector<ValueOrigin> domainLeaves;
  std::map<ValueOrigin, unsigned> domainLeafIds;
  struct FactoryFacts {
    std::vector<ItemBound> bounds;
    DomainEvidence evidence;
  };
  using RecipeKey =
      std::tuple<unsigned, std::vector<ValueOrigin>, std::vector<unsigned>>;
  std::map<RecipeKey, FactoryFacts> factoryFacts;
  const Declaration *owner = nullptr;
  bool infer, allowAdditional;
  unsigned rootInputs = 0;
  std::vector<DataPrecondition> requirements;
  std::vector<DataFact> assumptions;
  std::map<ValueOrigin, Type> valueTypes;
  std::map<ValueOrigin, uint64_t> constants;
  using ForwardedResult = std::optional<ValueOrigin>;
  struct ForwardingSummary {
    std::vector<ForwardedResult> outputs;
    uint64_t work = 0;
    unsigned height = 0;
  };
  // Checked declarations may grow between ContractCheck runs. Never retain
  // these descriptions in Semantics or in the capture-layout origin reader.
  std::map<unsigned, ForwardingSummary> forwardingMemo;
  std::set<unsigned> forwardingActive;
  struct Context {
    const Body &body;
    Facts inputs;
    Restrictions scoped;
    std::vector<std::optional<unsigned>> domains;
    ValueOrigins origins;
    InputValues inputValues;
    std::map<unsigned, ValueOrigin> forwardedValues;
    std::map<unsigned, Item> forwardedItems;
    unsigned base;
    unsigned depth;
    Context(Semantics &types, const Body &body, Facts inputs,
            Restrictions scoped, InputValues values, unsigned base,
            unsigned depth)
        : body(body), inputs(std::move(inputs)), scoped(std::move(scoped)),
          domains(body.domainBindings.size()), origins(types, body),
          inputValues(std::move(values)), base(base), depth(depth) {}
  };
  bool refuse(Span span, StringRef message) {
    return types.fail("source.scoped-domain", message, span);
  }
  bool bounded(unsigned depth, Span span) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "finite contract checking depth", span);
    return types.charge(1, span);
  }
  std::optional<ValueOrigin> value(Context &context, ValueId id, Span span) {
    auto local = context.origins.get(id, span);
    if (!local)
      return {};
    ValueOrigin result{context.base + local->first, local->second};
    std::optional<ValueOrigin> replacement;
    if (auto found = context.forwardedValues.find(local->first);
        found != context.forwardedValues.end())
      replacement = found->second;
    else if (local->first < context.inputValues.size())
      replacement = context.inputValues[local->first];
    if (replacement) {
      result = *replacement;
      if (!types.charge(result.second.size() + local->second.size() + 1, span))
        return {};
      result.second.insert(result.second.end(), local->second.begin(),
                           local->second.end());
    }
    const auto &type = context.body.values[id.index].type;
    if (!established(mathematical.record(result, type, span), span))
      return {};
    valueTypes.emplace(result, type);
    return result;
  }
  const ForwardingSummary *forwarding(unsigned id, unsigned depth, Span span) {
    const auto started = types.work.used;
    if (!bounded(depth, span) || depth > types.work.limits.callDepth) {
      if (!types.diagnostic)
        types.fail("source.limit", "helper forwarding depth", span);
      return nullptr;
    }
    if (auto found = forwardingMemo.find(id); found != forwardingMemo.end()) {
      const auto &summary = found->second;
      if (depth + summary.height > types.work.limits.expressionDepth ||
          depth + summary.height > types.work.limits.callDepth) {
        types.fail("source.limit", "helper forwarding depth", span);
        return nullptr;
      }
      // Replay logical extraction work, including nested descriptions. Cache
      // hits save computation, never the caller's allowance or depth checks.
      return types.charge(summary.work - 1, span) ? &summary : nullptr;
    }
    if (id >= declarations.size())
      return nullptr;
    const auto &callee = declarations[id];
    if (callee.abstract || callee.kind != Declaration::Kind::Math ||
        !callee.body || !forwardingActive.insert(id).second)
      return nullptr;
    auto leave = llvm::scope_exit([&] { forwardingActive.erase(id); });
    const auto &body = *callee.body;
    if (!types.charge(body.values.size() + body.operations.size() +
                          body.results.size() + 1,
                      span))
      return nullptr;
    ValueOrigins origins(types, body);
    std::vector<const Operation *> producers(body.values.size());
    for (const auto &op : body.operations) {
      if (!types.charge(op.results.size() + 1, op.span))
        return nullptr;
      for (auto result : op.results)
        producers[result.index] = &op;
    }
    ForwardingSummary summary;
    std::map<unsigned, ForwardedResult> results;
    std::function<ForwardedResult(ValueId, unsigned)> describe =
        [&](ValueId id, unsigned nesting) -> ForwardedResult {
      if (!bounded(depth + nesting, span))
        return {};
      summary.height = std::max(summary.height, nesting);
      auto origin = origins.get(id, span);
      if (!origin)
        return {};
      if (origin->first < body.inputs)
        return origin;
      auto found = results.find(origin->first);
      if (found == results.end()) {
        ForwardedResult result;
        const auto *producer = producers[origin->first];
        const auto *call =
            producer ? std::get_if<HelperCall>(&producer->action) : nullptr;
        if (call) {
          // Read only a returned value's dependency path. Checked callee
          // contracts justify internal calls, but supply no caller premises.
          // Even an ineligible callee consumes this depth before declining.
          // Preserve that observation when a later invocation uses the memo.
          summary.height = std::max(summary.height, nesting + 1);
          auto nested = forwarding(call->callee.index, depth + nesting + 1,
                                   producer->span);
          if (types.diagnostic)
            return {};
          if (nested) {
            summary.height =
                std::max(summary.height, nesting + 1 + nested->height);
            for (unsigned i = 0; i < producer->results.size(); ++i) {
              if (!types.charge(1, span))
                return {};
              if (producer->results[i].index != origin->first ||
                  i >= nested->outputs.size() || !nested->outputs[i])
                continue;
              const auto &[port, path] = *nested->outputs[i];
              if (port >= call->operands.size())
                return {};
              result = describe(call->operands[port], nesting + 1);
              if (result) {
                if (!types.charge(result->second.size() + path.size() + 1,
                                  span))
                  return {};
                result->second.insert(result->second.end(), path.begin(),
                                      path.end());
              }
            }
          }
        }
        found = results.emplace(origin->first, std::move(result)).first;
      }
      auto result = found->second;
      if (result) {
        if (!types.charge(result->second.size() + origin->second.size() + 1,
                          span))
          return {};
        result->second.insert(result->second.end(), origin->second.begin(),
                              origin->second.end());
      }
      return result;
    };
    for (auto output : body.results) {
      summary.outputs.push_back(describe(output, 0));
      if (types.diagnostic)
        return nullptr;
    }
    summary.work = types.work.used - started;
    return &forwardingMemo.emplace(id, std::move(summary)).first->second;
  }
  bool forward(Context &context, const HelperCall &call,
               ArrayRef<ValueId> outputs, unsigned depth, Span span) {
    auto descriptions = forwarding(call.callee.index, depth, span);
    if (!descriptions)
      return !types.diagnostic;
    for (unsigned i = 0; i < descriptions->outputs.size() && i < outputs.size();
         ++i) {
      const auto &description = descriptions->outputs[i];
      if (!types.charge(1, span))
        return false;
      if (description) {
        const auto &[port, path] = *description;
        if (port >= call.operands.size())
          return refuse(span, "forwarded result input coverage differs");
        auto origin = value(context, call.operands[port], span);
        if (!origin ||
            !types.charge(origin->second.size() + path.size() + 1, span))
          return false;
        origin->second.insert(origin->second.end(), path.begin(), path.end());
        context.forwardedValues.emplace(outputs[i].index, std::move(*origin));
        std::optional<Item> item;
        if (!fact(context, call.operands[port], item, span))
          return false;
        if (item) {
          if (!types.charge(item->path.size() + path.size() + 1, span))
            return false;
          item->path.insert(item->path.end(), path.begin(), path.end());
          context.forwardedItems.emplace(outputs[i].index, std::move(*item));
        }
      }
    }
    return true;
  }
  std::optional<ValueOrigin> select(Context &context,
                                    ArrayRef<ValueId> operands,
                                    const InputSelector &selector, Span span) {
    if (selector.port >= operands.size()) {
      refuse(span, "data precondition input is outside its call");
      return {};
    }
    auto result = value(context, operands[selector.port], span);
    if (!result || !types.charge(selector.path.size() + 1, span))
      return {};
    auto selected = types.projectedType(
        *owner, context.body.values[operands[selector.port].index].type,
        selector.path, span);
    if (!selected)
      return {};
    result->second.insert(result->second.end(), selector.path.begin(),
                          selector.path.end());
    if (!established(mathematical.record(*result, *selected, span), span))
      return {};
    valueTypes.emplace(*result, *selected);
    return result;
  }
  std::optional<DataFact> condition(Context &context,
                                    ArrayRef<ValueId> operands,
                                    const DataPrecondition &requirement,
                                    Span span) {
    auto left = select(context, operands, requirement.left, span);
    auto right = select(context, operands, requirement.right, span);
    if (!left || !right)
      return {};
    return DataFact{requirement.kind, *left, *right, requirement.leftAxis,
                    requirement.rightAxis};
  }
  std::optional<Natural> extent(const ValueOrigin &origin, unsigned axis) {
    auto found = valueTypes.find(origin);
    if (found == valueTypes.end())
      return {};
    auto *dimension = staticExtent(found->second, axis);
    return dimension ? std::optional<Natural>(*dimension) : std::nullopt;
  }
  bool established(facts::Status status, Span span) {
    if (status == facts::Status::Proven)
      return true;
    if (status == facts::Status::Capacity)
      return types.fail("source.limit", "mathematical fact checking work",
                        span);
    return types.fail("source.data-bound", "invalid mathematical premise",
                      span);
  }
  bool assume(DataFact fact, Span span) {
    if (!established(mathematical.assume(fact, span), span))
      return false;
    assumptions.push_back(std::move(fact));
    return true;
  }
  bool prove(const DataFact &needed, Span span) {
    auto status = mathematical.prove(needed, span);
    if (status == facts::Status::Proven)
      return true;
    // Only missing evidence may infer a declaration precondition. Exhaustion
    // is never a mathematical premise, even in a residual helper contract.
    if (status == facts::Status::Capacity)
      return established(status, span);
    if (types.diagnostic)
      return false;
    if (needed.kind == DataPrecondition::Kind::EqualExtent) {
      auto left = extent(needed.left, needed.leftAxis);
      auto right = extent(needed.right, needed.rightAxis);
      if (left && right && left->isClosed() && right->isClosed() &&
          *left != *right)
        return types.fail("source.data-bound", "fixed extents differ", span);
    }
    if (infer && owner->kind == Declaration::Kind::Math && !allowAdditional)
      return types.fail("source.data-bound",
                        "mathematical helper needs an explicit input condition",
                        owner->span, {span});
    if (infer && owner->kind == Declaration::Kind::Math &&
        needed.kind == DataPrecondition::Kind::IndexBound &&
        needed.left.first >= rootInputs && needed.right.first < rootInputs) {
      // A finite item is local to the callback. Lift its unmet container link
      // to an ordinary input extent condition on the enclosing helper.
      for (const auto &fact : assumptions) {
        if (!types.charge(
                fact.left.second.size() + fact.right.second.size() + 1, span))
          return false;
        if (fact.kind == DataPrecondition::Kind::IndexBound &&
            fact.left == needed.left && fact.right.first < rootInputs) {
          DataFact equal{DataPrecondition::Kind::EqualExtent, fact.right,
                         needed.right, fact.rightAxis, needed.rightAxis};
          return prove(equal, span);
        }
      }
    }
    if (!infer || owner->kind != Declaration::Kind::Math ||
        needed.left.first >= rootInputs || needed.right.first >= rootInputs)
      return types.fail(
          "source.data-bound",
          "data bound is not established for these immutable values", span);
    if (!types.charge(needed.left.second.size() + needed.right.second.size() +
                          requirements.size() + 1,
                      span))
      return false;
    DataPrecondition result{needed.kind,
                            {needed.left.first, needed.left.second, span},
                            {needed.right.first, needed.right.second, span},
                            needed.leftAxis,
                            needed.rightAxis,
                            span};
    if (!llvm::is_contained(requirements, result)) {
      if (requirements.size() >= 1024)
        return types.fail("source.limit",
                          "helper exceeds 1024 data preconditions", span);
      requirements.push_back(std::move(result));
    }
    return assume(needed, span);
  }
  unsigned newDomain(std::vector<ItemBound> facts = {}) {
    unsigned id = domainBounds.size();
    domainBounds.push_back(std::move(facts));
    domainEvidence.push_back({});
    return id;
  }
  std::optional<unsigned> recipe(const DomainBinding &binding,
                                 ArrayRef<ValueOrigin> operands,
                                 ArrayRef<unsigned> children, unsigned depth) {
    if (!bounded(depth, binding.span))
      return {};
    using Kind = DomainBinding::Kind;
    std::vector<ItemBound> facts;
    DomainEvidence evidence;
    if (binding.kind == Kind::Application) {
      if (!binding.factory ||
          binding.factory->declaration.index >= declarations.size()) {
        refuse(binding.span, "invalid domain factory reference");
        return {};
      }
      const auto &callee = declarations[binding.factory->declaration.index];
      if (!types.charge(operands.size() + children.size() + 1, binding.span))
        return {};
      RecipeKey key{callee.id.index, operands.vec(), children.vec()};
      if (auto found = factoryFacts.find(key); found != factoryFacts.end()) {
        if (!types.charge(found->second.bounds.size() +
                              found->second.evidence.children.size() + 1,
                          binding.span))
          return {};
        auto result = newDomain(found->second.bounds);
        domainEvidence[result] = found->second.evidence;
        return result;
      }
      // A generic module's implementation is not evidence available to its
      // clients. Only the checked recipe of a concrete factory supplies facts.
      if (!callee.abstract && callee.domainDefinition) {
        const auto &definition = *callee.domainDefinition;
        std::vector<unsigned> nested;
        for (const auto &node : definition.bindings) {
          if (node.parameter) {
            if (*node.parameter >= children.size()) {
              refuse(node.span, "domain parameter fact coverage differs");
              return {};
            }
            nested.push_back(children[*node.parameter]);
            continue;
          }
          std::vector<ValueOrigin> data;
          std::vector<unsigned> domains;
          if (!types.charge(node.operands.size() + node.children.size() + 1,
                            node.span))
            return {};
          for (auto operand : node.operands) {
            if (operand.index >= operands.size()) {
              refuse(node.span, "factory data fact coverage differs");
              return {};
            }
            data.push_back(operands[operand.index]);
          }
          for (auto child : node.children) {
            if (child >= nested.size()) {
              refuse(node.span, "factory child fact coverage differs");
              return {};
            }
            domains.push_back(nested[child]);
          }
          auto selected = recipe(node, data, domains, depth + 1);
          if (!selected)
            return {};
          nested.push_back(*selected);
        }
        if (definition.result >= nested.size()) {
          refuse(binding.span, "factory result fact coverage differs");
          return {};
        }
        facts = domainBounds[nested[definition.result]];
        evidence = domainEvidence[nested[definition.result]];
      }
      // Only structural constructors and exact operand origins are cached,
      // never a count or a caller premise. Each application has a fresh item
      // domain identity even when its evidence references the same leaves.
      factoryFacts.emplace(std::move(key), FactoryFacts{facts, evidence});
    } else if (binding.kind == Kind::Indices ||
               binding.kind == Kind::MatrixCoordinates) {
      if (operands.empty()) {
        refuse(binding.span, "index domain has no container");
        return {};
      }
      if (binding.kind == Kind::Indices)
        facts.push_back({{}, operands.front(), binding.axis});
      else {
        facts.push_back({{0}, operands.front(), 0});
        facts.push_back({{1}, operands.front(), 1});
      }
    } else if (binding.kind == Kind::Zip || binding.kind == Kind::Product) {
      for (unsigned i = 0; i < children.size(); ++i) {
        if (children[i] >= domainBounds.size()) {
          refuse(binding.span, "unknown domain child");
          return {};
        }
        for (const auto &bound : domainBounds[children[i]]) {
          if (!types.charge(bound.path.size() + bound.container.second.size() +
                                1,
                            binding.span))
            return {};
          auto nested = bound;
          nested.path.insert(nested.path.begin(), i);
          facts.push_back(std::move(nested));
        }
      }
    }
    if (binding.kind != Kind::Application) {
      DomainBinding constructor{};
      constructor.kind = binding.kind;
      constructor.axis = binding.axis;
      constructor.children = children.vec();
      for (const auto &operand : operands) {
        if (!types.charge(operand.second.size() + 1, binding.span))
          return {};
        auto [found, inserted] =
            domainLeafIds.emplace(operand, domainLeaves.size());
        if (inserted)
          domainLeaves.push_back(operand);
        constructor.operands.push_back({found->second});
      }
      evidence.node = cardinalityNode(constructor);
      evidence.children = children.vec();
    }
    if (!types.charge(facts.size() + evidence.children.size() + 1,
                      binding.span))
      return {};
    auto result = newDomain(std::move(facts));
    domainEvidence[result] = std::move(evidence);
    return result;
  }
  bool collectResult(Context &context, unsigned domain, ValueId output,
                     bool filtered, Span span) {
    auto result = value(context, output, span);
    if (!result)
      return false;
    facts::Work work([&](uint64_t amount) {
      return !types.diagnostic && types.charge(amount, span);
    });
    auto node = [&](facts::DomainRef id) { return domainEvidence[id].node; };
    auto child = [&](facts::DomainRef id, size_t index) -> facts::DomainRef {
      return domainEvidence[id].children[index];
    };
    auto extent = [&](facts::DomainExtent leaf, unsigned) {
      return mathematical.cardinality(domainLeaves[leaf.value], leaf.axis,
                                      span);
    };
    auto integer = [&](facts::DomainLeaf leaf,
                       unsigned) -> facts::Result<uint64_t> {
      auto found = constants.find(domainLeaves[leaf]);
      return found == constants.end()
                 ? facts::Result<uint64_t>{}
                 : facts::Result<uint64_t>{facts::Status::Proven,
                                           found->second};
    };
    auto same = [&](facts::DomainLeaf a, facts::DomainLeaf b, unsigned) {
      if (!work.charge(domainLeaves[a].second.size() +
                       domainLeaves[b].second.size() + 1))
        return facts::Status::Capacity;
      return domainLeaves[a] == domainLeaves[b] ? facts::Status::Proven
                                                : facts::Status::Unknown;
    };
    auto equal = [&](facts::DomainExtent a, facts::DomainExtent b, unsigned) {
      return mathematical.prove({DataPrecondition::Kind::EqualExtent,
                                 domainLeaves[a.value], domainLeaves[b.value],
                                 a.axis, b.axis},
                                span);
    };
    facts::DomainCardinality cardinality(
        work, {node, child, extent, integer, same, equal},
        types.work.limits.expressionDepth - context.depth);
    auto count = facts::collect(work, cardinality.count(domain), filtered);
    if (count.status == facts::Status::Capacity)
      return established(count.status, span);
    const auto &resultType = context.body.values[output.index].type;
    if (resultType.kind == Type::Kind::Builtin &&
        resultType.domain == "field_array") {
      const auto &size = resultType.arguments[1].dimension;
      if (size.isClosed() && count.status == facts::Status::Proven &&
          count.value->precision == facts::Precision::Exact &&
          count.value->value != size.closedValue())
        return types.fail("source.data-bound",
                          "fixed collection needs exact unfiltered cardinality",
                          span);
      // The type already supplies the result extent. Before closed formation,
      // neither an unknown count nor a symbolic result size justifies relating
      // that extent to the source domain. Publish no additional fixed facts.
      return !types.diagnostic;
    }
    if (count.status == facts::Status::Proven &&
        !established(
            mathematical.resultCardinality(*result, *count.value, span), span))
      return false;
    // Dynamic element traversal preserves an extent even when its numeric
    // count is unknown. Equality relates axes, never container identities.
    if (!filtered) {
      unsigned depth = 0;
      while (domainEvidence[domain].node.kind == facts::DomainKind::Zip) {
        if (!bounded(context.depth + ++depth, span))
          return false;
        if (domainEvidence[domain].children.empty())
          return refuse(span, "zip cardinality has no first child");
        domain = domainEvidence[domain].children.front();
      }
      const auto &source = domainEvidence[domain].node;
      if (source.kind == facts::DomainKind::Extent)
        return established(mathematical.resultExtent(
                               *result, domainLeaves[source.extent.value],
                               source.extent.axis, span),
                           span);
    }
    return !types.diagnostic;
  }
  bool finiteResult(Context &context, const HelperCall &call,
                    ArrayRef<ValueId> outputs, Span span) {
    const auto &callee = declarations[call.callee.index];
    if (context.body.mode != Body::Mode::Math || callee.abstract ||
        callee.kind != Declaration::Kind::Math || !callee.finiteDefinition ||
        !callee.body || callee.body->operations.size() != 1)
      return true;
    const auto *finite =
        std::get_if<FiniteApplication>(&callee.body->operations.front().action);
    if (!finite || finite->kind != FiniteApplication::Kind::Collect)
      return true;
    if (outputs.size() != 1 || call.domainArguments.size() != 1)
      return refuse(span, "finite definition result coverage differs");
    unsigned selected;
    return domain(context, call.domainArguments.front(), selected, span) &&
           collectResult(context, selected, outputs.front(),
                         bool(finite->predicate), span);
  }
  bool fact(Context &context, ValueId value, std::optional<Item> &result,
            Span span) {
    auto origin = context.origins.get(value, span);
    if (!origin)
      return false;
    result.reset();
    if (auto found = context.forwardedItems.find(origin->first);
        found != context.forwardedItems.end())
      result = found->second;
    else if (origin->first < context.inputs.size())
      result = context.inputs[origin->first];
    if (!result)
      return true;
    if (!types.charge(result->path.size() + origin->second.size() + 1, span))
      return false;
    result->path.insert(result->path.end(), origin->second.begin(),
                        origin->second.end());
    return true;
  }
  bool restriction(Context &context, unsigned index, OriginMap &result,
                   Span span) {
    if (index >= context.body.scopedBindings.size())
      return refuse(span, "scoped binding is outside its body");
    const auto &binding = context.body.scopedBindings[index];
    if (!binding.parameter || *binding.parameter >= context.scoped.size())
      return refuse(span, "scoped invocation requires a bound formal");
    if (!types.charge(context.scoped[*binding.parameter].size(), span))
      return false;
    result = context.scoped[*binding.parameter];
    return true;
  }
  bool domain(Context &context, unsigned index, unsigned &result, Span span,
              unsigned nested = 0) {
    if (!bounded(context.depth + nested, span))
      return false;
    if (index >= context.domains.size())
      return refuse(span, "finite domain is outside its body");
    if (context.domains[index]) {
      result = *context.domains[index];
      return true;
    }
    const auto &binding = context.body.domainBindings[index];
    if (binding.parameter)
      return refuse(span, "missing finite domain environment");
    std::vector<ValueOrigin> data;
    std::vector<unsigned> children;
    if (!types.charge(binding.operands.size() + binding.children.size() + 1,
                      binding.span))
      return false;
    for (auto operand : binding.operands) {
      auto origin = value(context, operand, binding.span);
      if (!origin)
        return false;
      data.push_back(std::move(*origin));
    }
    for (auto child : binding.children) {
      unsigned selected;
      if (child >= index)
        return refuse(binding.span, "domain child facts must precede use");
      if (!domain(context, child, selected, binding.span, nested + 1))
        return false;
      children.push_back(selected);
    }
    auto selected = recipe(binding, data, children, context.depth + nested + 1);
    if (!selected)
      return false;
    context.domains[index] = result = *selected;
    return true;
  }
  bool callback(Context &context, unsigned index, const OriginMap &expected,
                unsigned depth, Span span) {
    if (!bounded(depth, span) || index >= context.body.scopedBindings.size())
      return types.diagnostic ? false : refuse(span, "missing scoped binding");
    const auto &binding = context.body.scopedBindings[index];
    if (binding.parameter) {
      OriginMap actual;
      if (!restriction(context, index, actual, span))
        return false;
      if (!types.charge(actual.size(), span))
        return false;
      for (const auto &[input, domain] : actual) {
        auto promised = expected.find(input);
        if (promised == expected.end() || promised->second != domain)
          return refuse(
              span, "restricted callback requires the same input item origin");
      }
      return true;
    }
    if (!binding.computation || !binding.computation->body)
      return refuse(span, "missing scoped computation");
    const auto &computation = *binding.computation;
    const auto &nested = *computation.body;
    unsigned explicitInputs = computation.signature.inputs.size();
    if (nested.inputs != explicitInputs + binding.captures.size())
      return refuse(span, "scoped input coverage differs");
    if (!types.charge(nested.inputs + binding.scopedCaptures.size() +
                          binding.domainCaptures.size(),
                      span))
      return false;
    Facts inputs(nested.inputs);
    InputValues values(nested.inputs);
    if (!types.charge(expected.size(), span))
      return false;
    for (const auto &[input, domain] : expected) {
      if (input >= explicitInputs)
        return refuse(span, "item origin input is outside callback signature");
      inputs[input] = Item{domain, {}};
    }
    for (unsigned i = 0; i < binding.captures.size(); ++i) {
      values[explicitInputs + i] = value(context, binding.captures[i], span);
      if (!values[explicitInputs + i] ||
          !fact(context, binding.captures[i], inputs[explicitInputs + i], span))
        return false;
    }
    Restrictions selected(binding.scopedCaptures.size());
    for (unsigned i = 0; i < selected.size(); ++i)
      if (!restriction(context, binding.scopedCaptures[i], selected[i], span))
        return false;
    std::vector<unsigned> domains(binding.domainCaptures.size());
    for (unsigned i = 0; i < domains.size(); ++i)
      if (!domain(context, binding.domainCaptures[i], domains[i], span))
        return false;
    return body(nested, std::move(inputs), std::move(selected), domains,
                depth + 1, std::move(values));
  }
  bool call(Context &context, const HelperCall &call, unsigned depth,
            Span span) {
    if (call.callee.index >= declarations.size())
      return refuse(span, "unknown finite call target");
    const auto &callee = declarations[call.callee.index];
    if (call.scopedArguments.size() != callee.scopedInputs.size() ||
        call.domainArguments.size() != callee.domainInputs.size())
      return refuse(span, "static call argument coverage differs");
    if (!callee.dataPreconditions.empty() &&
        context.body.mode != Body::Mode::Math)
      return types.fail(
          "source.data-bound",
          "conditional mathematical helper requires a total context", span);
    for (const auto &requirement : callee.dataPreconditions) {
      auto needed = condition(context, call.operands, requirement, span);
      if (!needed)
        return false;
      if (!prove(*needed, span))
        return false;
    }
    for (unsigned i = 0; i < call.scopedArguments.size(); ++i) {
      OriginMap expected;
      const auto &parameter = callee.scopedInputs[i];
      if (!types.charge(parameter.itemOrigins.size(), span))
        return false;
      for (const auto &[input, formal] : parameter.itemOrigins) {
        unsigned selected;
        if (input >= parameter.signature.inputs.size() ||
            formal >= call.domainArguments.size() ||
            !domain(context, call.domainArguments[formal], selected, span))
          return types.diagnostic ? false : refuse(span, "invalid item origin");
        expected.emplace(input, selected);
      }
      if (!callback(context, call.scopedArguments[i], expected, depth + 1,
                    span))
        return false;
    }
    return true;
  }
  bool control(Context &context, const LocalControl &control, unsigned depth,
               Span span) {
    bool loop = control.kind == LocalControl::Kind::For;
    unsigned skipped = loop ? 2 : 1;
    if (control.operands.size() < skipped)
      return refuse(span, "control operand coverage differs");
    unsigned forwarded = control.operands.size() - skipped;
    std::vector<unsigned> domains(control.domainArguments.size());
    for (unsigned i = 0; i < domains.size(); ++i)
      if (!domain(context, control.domainArguments[i], domains[i], span))
        return false;
    for (const auto &region : control.regions) {
      if (!region || region->inputs < forwarded ||
          !types.charge(region->inputs, span))
        return types.diagnostic ? false
                                : refuse(span, "control input coverage");
      Facts inputs(region->inputs);
      InputValues values(region->inputs);
      unsigned prefix = region->inputs - forwarded;
      for (unsigned i = 0; i < forwarded; ++i) {
        // A carried value is a fresh successor even on a zero-trip path.
        if (loop && i < control.carried)
          continue;
        values[prefix + i] =
            value(context, control.operands[skipped + i], span);
        if (!values[prefix + i] || !fact(context, control.operands[skipped + i],
                                         inputs[prefix + i], span))
          return false;
      }
      for (const auto &origins : context.scoped)
        if (!types.charge(origins.size() + 1, span))
          return false;
      if (!body(*region, std::move(inputs), context.scoped, domains, depth + 1,
                std::move(values)))
        return false;
    }
    return true;
  }
  bool closedCallback(Context &context, const FiniteCallback &callback,
                      unsigned domain, unsigned itemInput, unsigned depth,
                      Span span) {
    if (!bounded(depth, span) || callback.helper.index >= declarations.size())
      return types.diagnostic ? false : refuse(span, "invalid finite helper");
    auto parentScope = mathematical.scope();
    auto savedAssumptions = assumptions.size();
    if (!established(mathematical.enter(span), span))
      return false;
    auto restore = llvm::scope_exit([&] {
      mathematical.restore(parentScope);
      assumptions.resize(savedAssumptions);
    });
    const auto &helper = declarations[callback.helper.index];
    unsigned explicitInputs = itemInput + 1;
    if (helper.inputs.size() != explicitInputs + callback.captures.size() ||
        domain >= domainBounds.size())
      return refuse(span, "finite helper input fact coverage differs");
    if (nextValue > std::numeric_limits<unsigned>::max() - explicitInputs)
      return types.fail("source.limit", "finite item fact identity limit",
                        span);
    std::vector<ValueOrigin> inputs;
    for (unsigned i = 0; i < explicitInputs; ++i) {
      inputs.push_back({nextValue++, {}});
      if (!established(
              mathematical.record(inputs.back(), helper.inputs[i].type, span),
              span))
        return false;
      valueTypes.emplace(inputs.back(), helper.inputs[i].type);
    }
    for (auto capture : callback.captures) {
      auto origin = value(context, capture, span);
      if (!origin)
        return false;
      inputs.push_back(std::move(*origin));
    }
    for (const auto &fact : domainBounds[domain]) {
      if (!types.charge(inputs[itemInput].second.size() + fact.path.size() + 1,
                        span))
        return false;
      auto index = inputs[itemInput];
      index.second = fact.path;
      if (!assume({DataPrecondition::Kind::IndexBound, std::move(index),
                   fact.container, 0, fact.axis},
                  span))
        return false;
    }
    auto selected =
        [&](const InputSelector &selector) -> std::optional<ValueOrigin> {
      if (selector.port >= inputs.size()) {
        refuse(span, "finite helper precondition port differs");
        return {};
      }
      if (!types.charge(selector.path.size() + 1, span))
        return {};
      auto result = inputs[selector.port];
      result.second.insert(result.second.end(), selector.path.begin(),
                           selector.path.end());
      auto type = types.projectedType(helper, helper.inputs[selector.port].type,
                                      selector.path, span);
      if (!type)
        return {};
      if (!established(mathematical.record(result, *type, span), span))
        return {};
      valueTypes.emplace(result, *type);
      return result;
    };
    for (const auto &requirement : helper.dataPreconditions) {
      auto left = selected(requirement.left),
           right = selected(requirement.right);
      if (!left || !right ||
          !prove({requirement.kind, *left, *right, requirement.leftAxis,
                  requirement.rightAxis},
                 span))
        return false;
    }
    return true;
  }
  bool closedFinite(Context &context, const FiniteComputation &finite,
                    unsigned depth, Span span, ValueId output) {
    if (!finite.domain || finite.domain->result >= finite.domain->nodes.size())
      return refuse(span, "invalid closed finite descriptor");
    std::vector<ValueOrigin> operands;
    for (auto operand : finite.domainOperands) {
      auto origin = value(context, operand, span);
      if (!origin)
        return false;
      operands.push_back(std::move(*origin));
    }
    std::vector<unsigned> domains;
    for (const auto &node : finite.domain->nodes) {
      std::vector<ValueOrigin> data;
      std::vector<unsigned> children;
      if (!types.charge(node.operands.size() + node.children.size() + 1, span))
        return false;
      for (auto operand : node.operands) {
        if (operand.index >= operands.size())
          return refuse(span, "closed descriptor input fact differs");
        data.push_back(operands[operand.index]);
      }
      for (auto child : node.children) {
        if (child >= domains.size())
          return refuse(span, "closed descriptor child fact differs");
        children.push_back(domains[child]);
      }
      auto selected = recipe(node, data, children, depth + 1);
      if (!selected)
        return false;
      domains.push_back(*selected);
    }
    auto constant = [&](ValueId id) -> std::optional<uint64_t> {
      auto found = constants.find(operands[id.index]);
      return found == constants.end() ? std::nullopt
                                      : std::optional<uint64_t>(found->second);
    };
    auto size = [&](ValueId id, unsigned axis) -> std::optional<uint64_t> {
      auto known = mathematical.cardinality(operands[id.index], axis, span);
      if (known.status == facts::Status::Capacity)
        established(known.status, span);
      return known.status == facts::Status::Proven &&
                     known.value->precision == facts::Precision::Exact
                 ? std::optional<uint64_t>(known.value->value)
                 : std::nullopt;
    };
    auto same = [&](ValueId a, ValueId b) {
      return operands[a.index] == operands[b.index];
    };
    auto equal = [&](ValueId a, unsigned aa, ValueId b, unsigned ba) {
      return prove({DataPrecondition::Kind::EqualExtent, operands[a.index],
                    operands[b.index], aa, ba},
                   span);
    };
    auto bound = [&](ValueId index, ValueId container, unsigned axis) {
      return prove({DataPrecondition::Kind::IndexBound, operands[index.index],
                    operands[container.index], 0, axis},
                   span);
    };
    if (!checkFiniteFormation(types, finite,
                              context.body.values[output.index].type,
                              context.body.mode == Body::Mode::Math, span,
                              {constant, size, same, equal, bound}))
      return false;
    unsigned selected = domains[finite.domain->result];
    if (!closedCallback(context, finite.body, selected,
                        finiteItemInput(finite.kind), depth + 1, span))
      return false;
    if (finite.predicate &&
        !closedCallback(context, *finite.predicate, selected,
                        finiteItemInput(finite.kind, true), depth + 1, span))
      return false;
    return finite.kind != FiniteApplication::Kind::Collect ||
           context.body.mode != Body::Mode::Math ||
           collectResult(context, selected, output, bool(finite.predicate),
                         span);
  }
  bool body(const Body &source, Facts inputs, Restrictions scoped,
            ArrayRef<unsigned> environment, unsigned depth,
            InputValues values = {}) {
    if (!bounded(depth, {}) ||
        !types.charge(source.values.size() + source.domainBindings.size() +
                          source.scopedBindings.size() +
                          source.operations.size(),
                      {}))
      return false;
    if (inputs.size() != source.inputs || source.inputs > source.values.size())
      return refuse({}, "body input coverage differs");
    if (source.values.size() > std::numeric_limits<unsigned>::max() - nextValue)
      return types.fail("source.limit", "data provenance identity limit", {});
    auto parentScope = mathematical.scope();
    auto savedAssumptions = assumptions.size();
    if (!established(mathematical.enter({}), {}))
      return false;
    auto restore = llvm::scope_exit([&] {
      mathematical.restore(parentScope);
      assumptions.resize(savedAssumptions);
    });
    unsigned base = nextValue;
    nextValue += source.values.size();
    if (values.empty())
      values.resize(source.inputs);
    if (values.size() != source.inputs)
      return refuse({}, "data input identity coverage differs");
    Context context(types, source, std::move(inputs), std::move(scoped),
                    std::move(values), base, depth);
    if (depth == 1) {
      std::vector<ValueId> arguments;
      for (unsigned i = 0; i < source.inputs; ++i)
        arguments.push_back({i});
      for (const auto &requirement : owner->dataPreconditions) {
        auto assumed =
            condition(context, arguments, requirement, requirement.span);
        if (!assumed)
          return false;
        if (!assume(std::move(*assumed), requirement.span))
          return false;
      }
    }
    for (unsigned i = 0; i < source.domainBindings.size(); ++i) {
      const auto &binding = source.domainBindings[i];
      if (binding.parameter) {
        if (*binding.parameter >= environment.size())
          return refuse(binding.span, "missing finite domain environment");
        context.domains[i] = environment[*binding.parameter];
      }
      // Constructor order is structural. Semantic operand evidence is read
      // only when used, after preceding helper calls discharge their premises.
      if (!types.charge(binding.children.size() + 1, binding.span))
        return false;
      for (auto child : binding.children)
        if (child >= i)
          return refuse(binding.span, "domain child facts must precede use");
    }
    for (unsigned i = 0; i < context.inputs.size(); ++i) {
      const auto &item = context.inputs[i];
      if (!item)
        continue;
      if (item->domain >= domainBounds.size())
        return refuse({}, "unknown item domain facts");
      auto root = value(context, ValueId{i}, {});
      if (!root)
        return false;
      for (const auto &bound : domainBounds[item->domain]) {
        if (!types.charge(bound.path.size() + root->second.size() + 1, {}))
          return false;
        if (bound.path.size() < item->path.size() ||
            !std::equal(item->path.begin(), item->path.end(),
                        bound.path.begin()))
          continue;
        auto index = *root;
        index.second.insert(index.second.end(),
                            bound.path.begin() + item->path.size(),
                            bound.path.end());
        if (!assume({DataPrecondition::Kind::IndexBound, std::move(index),
                     bound.container, 0, bound.axis},
                    {}))
          return false;
      }
    }
    for (const auto &op : source.operations) {
      if (!bounded(depth, op.span))
        return false;
      const auto *mathConstant = std::get_if<MathValue>(&op.action);
      const auto *localConstant = std::get_if<LocalPrimitive>(&op.action);
      bool totalConstant =
          mathConstant &&
          mathConstant->identity == MathematicalIdentity::IndexConstant;
      bool checkedConstant =
          localConstant && localConstant->contract == "index.constant";
      if ((totalConstant || checkedConstant) && op.results.size() == 1) {
        auto identity = value(context, op.results.front(), op.span);
        if (!identity)
          return false;
        std::optional<uint64_t> constant;
        const auto &statics = totalConstant ? mathConstant->staticArguments
                                            : localConstant->staticArguments;
        if (!statics.empty()) {
          const auto &natural = statics.front().dimension;
          if (natural.isClosed())
            constant = natural.closedValue();
        } else {
          uint64_t n;
          StringRef literal =
              totalConstant ? StringRef(mathConstant->literal)
              : localConstant->parameters.empty()
                  ? StringRef()
                  : StringRef(localConstant->parameters.front());
          if (!literal.getAsInteger(10, n))
            constant = n;
        }
        if (constant) {
          if (!established(mathematical.constant(*identity, *constant, op.span),
                           op.span))
            return false;
          constants.emplace(*identity, *constant);
        }
      }
      if (const auto *math = std::get_if<MathValue>(&op.action);
          math && (math->identity == MathematicalIdentity::ContainerAt ||
                   math->identity == MathematicalIdentity::MatrixAt)) {
        bool matrix = math->identity == MathematicalIdentity::MatrixAt;
        if (math->operands.size() != (matrix ? 3u : 2u))
          return types.fail("source.data-bound",
                            "total access operand count differs", op.span);
        auto container = value(context, math->operands.front(), op.span);
        if (!container)
          return false;
        for (unsigned axis = 0; axis < (matrix ? 2u : 1u); ++axis) {
          auto index = value(context, math->operands[axis + 1], op.span);
          if (!index)
            return false;
          DataFact needed{DataPrecondition::Kind::IndexBound, *index,
                          *container, 0, axis};
          if (!prove(needed, op.span))
            return false;
        }
      }
      if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
        OriginMap required;
        if (!restriction(context, invoke->binding, required, op.span))
          return false;
        if (!types.charge(required.size(), op.span))
          return false;
        for (const auto &[input, domain] : required) {
          std::optional<Item> actual;
          if (input >= invoke->operands.size() ||
              !fact(context, invoke->operands[input], actual, op.span))
            return types.diagnostic ? false : refuse(op.span, "missing item");
          if (!actual || !actual->path.empty() || actual->domain != domain)
            return refuse(op.span, "restricted callback requires a whole item "
                                   "from its declared domain");
        }
      } else if (const auto *helper = std::get_if<HelperCall>(&op.action)) {
        if (!call(context, *helper, depth + 1, op.span) ||
            !forward(context, *helper, op.results, depth + 1, op.span) ||
            !finiteResult(context, *helper, op.results, op.span))
          return false;
      } else if (const auto *finite =
                     std::get_if<FiniteApplication>(&op.action)) {
        unsigned selected;
        if (!domain(context, finite->domain, selected, op.span) ||
            !callback(context, finite->body,
                      {{finiteItemInput(finite->kind), selected}}, depth + 1,
                      op.span) ||
            (finite->predicate &&
             !callback(context, *finite->predicate,
                       {{finiteItemInput(finite->kind, true), selected}},
                       depth + 1, op.span)))
          return false;
      } else if (const auto *finite =
                     std::get_if<FiniteComputation>(&op.action)) {
        if (op.results.size() != 1 ||
            !closedFinite(context, *finite, depth + 1, op.span,
                          op.results.front()))
          return false;
      } else if (const auto *region = std::get_if<LocalControl>(&op.action)) {
        if (!control(context, *region, depth + 1, op.span))
          return false;
      } else if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        if (!repeat->region ||
            repeat->region->inputs !=
                1 + repeat->carried.size() + repeat->captures.size())
          return refuse(op.span, "protocol region input coverage differs");
        if (!types.charge(repeat->region->inputs, op.span))
          return false;
        Facts nested(repeat->region->inputs);
        InputValues values(repeat->region->inputs);
        for (unsigned i = 0; i < repeat->captures.size(); ++i) {
          auto port = 1 + repeat->carried.size() + i;
          values[port] = value(context, repeat->captures[i], op.span);
          if (!values[port] ||
              !fact(context, repeat->captures[i], nested[port], op.span))
            return false;
        }
        if (!body(*repeat->region, std::move(nested), {}, {}, depth + 1,
                  std::move(values)))
          return false;
      }
    }
    // Retain checking of unused recipes without borrowing evidence from an
    // unchecked operation or admitting unrelated constructors at a consumer.
    for (unsigned i = 0; i < context.domains.size(); ++i) {
      unsigned selected;
      if (!domain(context, i, selected, source.domainBindings[i].span))
        return false;
    }
    return true;
  }

public:
  ContractCheck(Semantics &types, ArrayRef<Declaration> declarations,
                bool infer = false, bool allowAdditional = false)
      : types(types), mathematical(types), declarations(declarations),
        infer(infer), allowAdditional(allowAdditional) {}
  std::vector<DataPrecondition> takeRequirements() {
    return std::move(requirements);
  }
  bool run(const Declaration &decl, const Body &source) {
    owner = &decl;
    rootInputs = source.inputs;
    requirements = decl.dataPreconditions;
    if (!types.charge(source.inputs + decl.domainInputs.size() +
                          decl.scopedInputs.size(),
                      decl.span))
      return false;
    if (infer)
      return body(source, Facts(source.inputs), {}, {}, 1);
    std::vector<unsigned> domains;
    for (unsigned i = 0; i < decl.domainInputs.size(); ++i)
      domains.push_back(newDomain());
    Restrictions selected;
    for (const auto &parameter : decl.scopedInputs) {
      OriginMap origins;
      if (!types.charge(parameter.itemOrigins.size(), parameter.span))
        return false;
      for (const auto &[input, formal] : parameter.itemOrigins) {
        if (input >= parameter.signature.inputs.size() ||
            formal >= domains.size())
          return refuse(parameter.span, "invalid declared item origin");
        origins.emplace(input, domains[formal]);
      }
      selected.push_back(std::move(origins));
    }
    return body(source, Facts(source.inputs), std::move(selected), domains, 1);
  }
};
} // namespace
bool checkFiniteContracts(Semantics &types, ArrayRef<Declaration> declarations,
                          const Declaration &decl, const Body &body) {
  return ContractCheck(types, declarations).run(decl, body);
}
std::optional<std::vector<DataPrecondition>>
deriveDataPreconditions(Semantics &types, ArrayRef<Declaration> declarations,
                        const Declaration &decl, const Body &body,
                        bool allowAdditional) {
  ContractCheck check(types, declarations, true, allowAdditional);
  if (!check.run(decl, body))
    return {};
  return check.takeRequirements();
}
} // namespace zkc::language::detail
