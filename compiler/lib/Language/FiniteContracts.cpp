#include "FiniteContracts.h"
#include "DataRequirements.h"
#include "FiniteFormation.h"
#include "ValueOrigins.h"
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
struct DataFact {
  DataPrecondition::Kind kind;
  ValueOrigin left, right;
  unsigned leftAxis = 0, rightAxis = 0;
};

// A generic declaration is checked with distinct abstract domain identities.
// Literal bodies are checked at their binding occurrence, after all eager
// arguments have been elaborated. This makes named argument order irrelevant
// to checking without changing when captures or ordinary values are evaluated.
class ContractCheck {
  Semantics &types;
  ArrayRef<Declaration> declarations;
  unsigned nextValue = 0;
  std::vector<std::vector<ItemBound>> domainBounds;
  using RecipeKey =
      std::tuple<unsigned, std::vector<ValueOrigin>, std::vector<unsigned>>;
  std::map<RecipeKey, std::vector<ItemBound>> factoryFacts;
  const Declaration *owner = nullptr;
  bool infer, allowAdditional;
  unsigned rootInputs = 0;
  std::vector<DataPrecondition> requirements;
  std::vector<DataFact> assumptions;
  std::map<ValueOrigin, Type> valueTypes;
  std::map<ValueOrigin, uint64_t> constants;
  struct Context {
    const Body &body;
    Facts inputs;
    Restrictions scoped;
    std::vector<unsigned> domains;
    ValueOrigins origins;
    InputValues inputValues;
    unsigned base;
    Context(Semantics &types, const Body &body, Facts inputs,
            Restrictions scoped, InputValues values, unsigned base)
        : body(body), inputs(std::move(inputs)), scoped(std::move(scoped)),
          origins(types, body), inputValues(std::move(values)), base(base) {}
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
    if (local->first < context.inputValues.size() &&
        context.inputValues[local->first]) {
      result = *context.inputValues[local->first];
      if (!types.charge(result.second.size() + local->second.size() + 1, span))
        return {};
      result.second.insert(result.second.end(), local->second.begin(),
                           local->second.end());
    }
    valueTypes.emplace(result, context.body.values[id.index].type);
    return result;
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
    if (found == valueTypes.end() || axis)
      return {};
    const auto &type = found->second;
    if (type.kind == Type::Kind::Array)
      return type.dimension;
    if (type.kind == Type::Kind::Builtin && type.domain == "field_array" &&
        type.arguments.size() == 2)
      return type.arguments[1].dimension;
    return {};
  }
  bool equalExtent(const ValueOrigin &left, unsigned leftAxis,
                   const ValueOrigin &right, unsigned rightAxis, Span span) {
    auto a = extent(left, leftAxis), b = extent(right, rightAxis);
    if (a && b && *a == *b)
      return true;
    using Extent = std::pair<ValueOrigin, unsigned>;
    std::vector<Extent> pending{{left, leftAxis}};
    std::set<Extent> seen;
    while (!pending.empty()) {
      auto current = std::move(pending.back());
      pending.pop_back();
      if (current == Extent{right, rightAxis})
        return true;
      if (!seen.insert(current).second)
        continue;
      if (!types.charge(assumptions.size() + 1, span))
        return false;
      for (const auto &fact : assumptions)
        if (fact.kind == DataPrecondition::Kind::EqualExtent) {
          Extent lhs{fact.left, fact.leftAxis}, rhs{fact.right, fact.rightAxis};
          if (current == lhs)
            pending.push_back(rhs);
          if (current == rhs)
            pending.push_back(lhs);
        }
    }
    return false;
  }
  bool holds(const DataFact &needed, Span span) {
    if (needed.kind == DataPrecondition::Kind::EqualExtent)
      return equalExtent(needed.left, needed.leftAxis, needed.right,
                         needed.rightAxis, span);
    auto constant = constants.find(needed.left);
    auto size = extent(needed.right, needed.rightAxis);
    if (constant != constants.end() && size && size->isClosed() &&
        constant->second < size->closedValue())
      return true;
    if (!types.charge(assumptions.size() + 1, span))
      return false;
    for (const auto &fact : assumptions)
      if (fact.kind == DataPrecondition::Kind::IndexBound &&
          fact.left == needed.left &&
          equalExtent(fact.right, fact.rightAxis, needed.right,
                      needed.rightAxis, span))
        return true;
    return false;
  }
  bool prove(const DataFact &needed, Span span) {
    if (holds(needed, span))
      return true;
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
      for (const auto &fact : assumptions)
        if (fact.kind == DataPrecondition::Kind::IndexBound &&
            fact.left == needed.left && fact.right.first < rootInputs) {
          DataFact equal{DataPrecondition::Kind::EqualExtent, fact.right,
                         needed.right, fact.rightAxis, needed.rightAxis};
          return prove(equal, span);
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
    assumptions.push_back(needed);
    return true;
  }
  unsigned newDomain(std::vector<ItemBound> facts = {}) {
    unsigned id = domainBounds.size();
    domainBounds.push_back(std::move(facts));
    return id;
  }
  std::optional<unsigned> recipe(const DomainBinding &binding,
                                 ArrayRef<ValueOrigin> operands,
                                 ArrayRef<unsigned> children, unsigned depth) {
    if (!bounded(depth, binding.span))
      return {};
    using Kind = DomainBinding::Kind;
    std::vector<ItemBound> facts;
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
        if (!types.charge(found->second.size() + 1, binding.span))
          return {};
        return newDomain(found->second);
      }
      // A generic component's implementation is not evidence available to its
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
      }
      // This cache stores only structural item/container facts, which do not
      // depend on static sizes. Each application still has a fresh item-domain
      // identity; caching evidence never equates two domain instances.
      factoryFacts.emplace(std::move(key), facts);
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
    if (!types.charge(facts.size() + 1, binding.span))
      return {};
    return newDomain(std::move(facts));
  }
  bool fact(Context &context, ValueId value, std::optional<Item> &result,
            Span span) {
    auto origin = context.origins.get(value, span);
    if (!origin)
      return false;
    result.reset();
    if (origin->first >= context.inputs.size() ||
        !context.inputs[origin->first])
      return true;
    result = context.inputs[origin->first];
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
  bool domain(Context &context, unsigned index, unsigned &result, Span span) {
    if (index >= context.domains.size())
      return refuse(span, "finite domain is outside its body");
    result = context.domains[index];
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
      valueTypes.emplace(inputs.back(), helper.inputs[i].type);
    }
    for (auto capture : callback.captures) {
      auto origin = value(context, capture, span);
      if (!origin)
        return false;
      inputs.push_back(std::move(*origin));
    }
    for (const auto &fact : domainBounds[domain]) {
      auto index = inputs[itemInput];
      index.second = fact.path;
      assumptions.push_back({DataPrecondition::Kind::IndexBound,
                             std::move(index), fact.container, 0, fact.axis});
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
                    unsigned depth, Span span, const Type &result) {
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
      auto known = extent(operands[id.index], axis);
      return known && known->isClosed()
                 ? std::optional<uint64_t>(known->closedValue())
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
    if (!checkFiniteFormation(types, finite, result,
                              context.body.mode == Body::Mode::Math, span,
                              {constant, size, same, equal, bound}))
      return false;
    unsigned selected = domains[finite.domain->result];
    return closedCallback(context, finite.body, selected,
                          finiteItemInput(finite.kind), depth + 1, span) &&
           (!finite.predicate ||
            closedCallback(context, *finite.predicate, selected,
                           finiteItemInput(finite.kind, true), depth + 1,
                           span));
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
    unsigned base = nextValue;
    nextValue += source.values.size();
    if (values.empty())
      values.resize(source.inputs);
    if (values.size() != source.inputs)
      return refuse({}, "data input identity coverage differs");
    Context context(types, source, std::move(inputs), std::move(scoped),
                    std::move(values), base);
    if (depth == 1) {
      std::vector<ValueId> arguments;
      for (unsigned i = 0; i < source.inputs; ++i)
        arguments.push_back({i});
      for (const auto &requirement : owner->dataPreconditions) {
        auto assumed =
            condition(context, arguments, requirement, requirement.span);
        if (!assumed)
          return false;
        assumptions.push_back(std::move(*assumed));
      }
    }
    for (const auto &binding : source.domainBindings) {
      if (binding.parameter) {
        if (*binding.parameter >= environment.size())
          return refuse(binding.span, "missing finite domain environment");
        context.domains.push_back(environment[*binding.parameter]);
      } else {
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
          if (child >= context.domains.size())
            return refuse(binding.span, "domain child facts must precede use");
          children.push_back(context.domains[child]);
        }
        auto selected = recipe(binding, data, children, depth + 1);
        if (!selected)
          return false;
        context.domains.push_back(*selected);
      }
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
        assumptions.push_back({DataPrecondition::Kind::IndexBound,
                               std::move(index), bound.container, 0,
                               bound.axis});
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
        if (constant)
          constants.emplace(*identity, *constant);
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
        if (!call(context, *helper, depth + 1, op.span))
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
                          source.values[op.results.front().index].type))
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
    return true;
  }

public:
  ContractCheck(Semantics &types, ArrayRef<Declaration> declarations,
                bool infer = false, bool allowAdditional = false)
      : types(types), declarations(declarations), infer(infer),
        allowAdditional(allowAdditional) {}
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
