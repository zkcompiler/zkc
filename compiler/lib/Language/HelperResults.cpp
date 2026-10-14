#include "HelperResults.h"
#include "FiniteCardinality.h"
#include "MathematicalFacts.h"
#include "llvm/ADT/ScopeExit.h"

using namespace llvm;
namespace zkc::language::detail {
class HelperResults::Extraction {
  HelperResults &reader;
  Semantics &types;
  const Declaration &owner;
  const Body &body;
  ValueOrigins &origins;
  std::map<ValueOrigin, HelperResult> values;
  std::optional<ValueOrigin> pending;
  unsigned baseDepth, height = 0;
  Span span;
  facts::Work work;
  std::vector<ResultShape> shapes{ResultShape{}};
  std::map<unsigned, unsigned> bodyDomains;
  using FactoryKey =
      std::tuple<unsigned, std::vector<unsigned>, std::vector<unsigned>>;
  std::map<FactoryKey, unsigned> factories;

  bool enter(unsigned depth) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "helper result domain depth", span);
    return types.charge(1, span);
  }
  unsigned remember(ResultShape shape) {
    unsigned id = shapes.size();
    shapes.push_back(std::move(shape));
    return id;
  }
  std::optional<uint64_t> integer(ValueId id) {
    auto origin = origins.select(id, {}, span);
    if (!origin || !origin->second.empty())
      return {};
    const auto *op = origins.producer({origin->first}, span);
    const auto *math = op ? std::get_if<MathValue>(&op->action) : nullptr;
    if (!math || math->identity != MathematicalIdentity::IndexConstant)
      return {};
    if (!math->staticArguments.empty()) {
      const auto &n = math->staticArguments.front().dimension;
      return n.isClosed() ? std::optional<uint64_t>(n.closedValue())
                          : std::nullopt;
    }
    uint64_t n;
    return StringRef(math->literal).getAsInteger(10, n)
               ? std::nullopt
               : std::optional<uint64_t>(n);
  }
  HelperResult value(ValueId id, ArrayRef<unsigned> path = {}) {
    auto origin = origins.select(id, path, span);
    if (!origin)
      return {};
    if (auto found = values.find(*origin); found != values.end())
      return found->second;
    if (!pending)
      pending = std::move(origin);
    return {};
  }
  ResultShape extent(ValueId id, unsigned axis) {
    auto result = value(id);
    if (result.forwarded)
      return {*result.forwarded,
              axis,
              {},
              axis == 0 ? result.shape.count : std::nullopt,
              false};
    return axis == 0 ? result.shape : ResultShape{};
  }
  unsigned domain(const DomainBinding &node, ArrayRef<ValueId> operands,
                  ArrayRef<unsigned> children, unsigned depth) {
    if (pending || !enter(depth))
      return 0;
    if (node.kind == DomainBinding::Kind::Application) {
      if (!node.factory ||
          node.factory->declaration.index >= reader.declarations.size())
        return remember({});
      unsigned index = node.factory->declaration.index;
      std::vector<unsigned> inputs;
      for (auto operand : operands)
        inputs.push_back(operand.index);
      FactoryKey key{index, std::move(inputs), children.vec()};
      if (auto found = factories.find(key); found != factories.end())
        return found->second;
      const auto &callee = reader.declarations[index];
      if (callee.abstract || !callee.domainDefinition)
        return remember({});
      const auto &recipe = *callee.domainDefinition;
      auto result = domains(recipe.bindings, recipe.result, operands, children,
                            depth + 1);
      if (!pending && !types.diagnostic)
        factories.emplace(std::move(key), result);
      return result;
    }
    DomainBinding mapped = node;
    mapped.operands = operands.vec();
    auto view = cardinalityNode(mapped);
    if (view.kind == facts::DomainKind::Zip)
      return children.empty() ? remember({}) : children.front();
    if (view.kind == facts::DomainKind::Extent)
      return remember(
          extent({static_cast<unsigned>(view.extent.value)}, view.extent.axis));
    ResultShape result;
    if (view.kind == facts::DomainKind::Range) {
      auto lower = integer({static_cast<unsigned>(view.lower)}),
           upper = integer({static_cast<unsigned>(view.upper)});
      if (lower && upper)
        result.count = facts::range(work, *lower, *upper).value;
    } else if (view.kind == facts::DomainKind::Product ||
               view.kind == facts::DomainKind::MatrixCoordinates) {
      SmallVector<facts::Result<facts::Cardinality>> counts;
      auto append = [&](const ResultShape &shape) {
        counts.push_back(
            shape.count
                ? facts::Result<facts::Cardinality>{facts::Status::Proven,
                                                    shape.count}
                : facts::Result<facts::Cardinality>{});
      };
      if (view.kind == facts::DomainKind::MatrixCoordinates) {
        append(extent({static_cast<unsigned>(view.extent.value)}, 0));
        append(extent({static_cast<unsigned>(view.extent.value)}, 1));
      } else {
        for (auto child : children)
          append(shapes[child]);
      }
      result.count = facts::product(work, counts).value;
    }
    return remember(std::move(result));
  }
  unsigned domains(ArrayRef<DomainBinding> nodes, unsigned selected,
                   ArrayRef<ValueId> data, ArrayRef<unsigned> parameters,
                   unsigned depth) {
    if (!enter(depth) || !types.charge(nodes.size(), span))
      return remember({});
    SmallVector<unsigned> nested;
    for (const auto &node : nodes) {
      if (pending || types.diagnostic)
        return remember({});
      if (node.parameter) {
        if (*node.parameter >= parameters.size()) {
          types.fail("source.scoped-domain",
                     "helper domain parameter coverage differs", span);
          return 0;
        }
        nested.push_back(parameters[*node.parameter]);
        continue;
      }
      if (!types.charge(node.operands.size() + node.children.size() + 1, span))
        return remember({});
      SmallVector<ValueId> operands;
      SmallVector<unsigned> children;
      for (auto operand : node.operands) {
        if (operand.index >= data.size()) {
          types.fail("source.scoped-domain",
                     "helper domain data coverage differs", span);
          return 0;
        }
        operands.push_back(data[operand.index]);
      }
      for (auto child : node.children) {
        if (child >= nested.size()) {
          types.fail("source.scoped-domain",
                     "helper domain child coverage differs", span);
          return 0;
        }
        children.push_back(nested[child]);
      }
      nested.push_back(domain(node, operands, children, depth + 1));
    }
    return selected < nested.size() ? nested[selected] : remember({});
  }
  unsigned bodyDomain(unsigned selected, unsigned depth = 0) {
    if (pending || !enter(depth))
      return 0;
    if (auto found = bodyDomains.find(selected); found != bodyDomains.end())
      return found->second;
    if (selected >= body.domainBindings.size()) {
      types.fail("source.scoped-domain", "helper domain is outside its body",
                 span);
      return 0;
    }
    const auto &node = body.domainBindings[selected];
    unsigned result;
    if (node.parameter) {
      result = remember({{}, 0, *node.parameter, {}, false});
    } else {
      SmallVector<unsigned> children;
      for (auto child : node.children) {
        if (pending || types.diagnostic)
          return 0;
        children.push_back(bodyDomain(child, depth + 1));
      }
      result = domain(node, node.operands, children, depth + 1);
    }
    if (!pending && !types.diagnostic)
      bodyDomains.emplace(selected, result);
    return result;
  }
  static void filter(ResultShape &shape) {
    shape.filtered = true;
    if (shape.count && shape.count->value)
      shape.count->precision = facts::Precision::Upper;
  }
  HelperResult call(const HelperCall &call, unsigned output,
                    ArrayRef<unsigned> path) {
    auto nested =
        reader.get(call.callee.index, output, path, span, baseDepth + 1);
    if (!nested)
      return {};
    height = std::max(height, 1 + nested->height);
    if (nested->forwarded) {
      const auto &[port, selector] = *nested->forwarded;
      if (port >= call.operands.size()) {
        types.fail("source.scoped-domain",
                   "helper result input coverage differs", span);
        return {};
      }
      return value(call.operands[port], selector);
    }
    HelperResult result;
    if (nested->shape.input) {
      const auto &[port, selector] = *nested->shape.input;
      if (port >= call.operands.size()) {
        types.fail("source.scoped-domain",
                   "helper result input coverage differs", span);
        return {};
      }
      auto actual = value(call.operands[port], selector);
      result.shape = actual.forwarded ? ResultShape{actual.forwarded,
                                                    nested->shape.axis,
                                                    {},
                                                    nested->shape.axis == 0
                                                        ? actual.shape.count
                                                        : std::nullopt,
                                                    false}
                     : nested->shape.axis == 0 ? actual.shape
                                               : ResultShape{};
    } else if (nested->shape.domain) {
      if (*nested->shape.domain >= call.domainArguments.size()) {
        types.fail("source.scoped-domain",
                   "helper result domain coverage differs", span);
        return {};
      }
      result.shape =
          shapes[bodyDomain(call.domainArguments[*nested->shape.domain])];
    } else {
      result.shape = nested->shape;
    }
    if (nested->shape.filtered)
      filter(result.shape);
    return result;
  }
  HelperResult describe(const ValueOrigin &origin) {
    if (origin.first < body.inputs)
      return {origin, {}, 0};
    const auto *producer = origins.producer({origin.first}, span);
    if (!producer)
      return {};
    if (const auto *helper = std::get_if<HelperCall>(&producer->action))
      for (unsigned i = 0; i < producer->results.size(); ++i)
        if (producer->results[i].index == origin.first)
          return call(*helper, i, origin.second);
    if (!origin.second.empty() ||
        staticExtent(body.values[origin.first].type, 0))
      return {};
    HelperResult result;
    if (const auto *finite = std::get_if<FiniteApplication>(&producer->action);
        finite && finite->kind == FiniteApplication::Kind::Collect) {
      result.shape = shapes[bodyDomain(finite->domain)];
      if (finite->predicate)
        filter(result.shape);
    } else if (const auto *finite =
                   std::get_if<FiniteComputation>(&producer->action);
               finite && finite->kind == FiniteApplication::Kind::Collect &&
               finite->domain) {
      result.shape =
          shapes[domains(finite->domain->nodes, finite->domain->result,
                         finite->domainOperands, {}, 0)];
      if (finite->predicate)
        filter(result.shape);
    }
    return result;
  }

public:
  Extraction(HelperResults &reader, const Declaration &owner,
             ValueOrigins &origins, unsigned depth, Span span)
      : reader(reader), types(reader.types), owner(owner), body(*owner.body),
        origins(origins), baseDepth(depth), span(span),
        work([&](uint64_t amount) {
          return !types.diagnostic && types.charge(amount, this->span);
        }) {}
  HelperResult run(unsigned output, ArrayRef<unsigned> path) {
    auto requested = origins.select(body.results[output], path, span);
    if (!requested)
      return {};
    // Iterative dependency traversal: sequential SSA chains consume work, not
    // expression or call depth. Only interprocedural calls use call depth.
    std::vector<ValueOrigin> stack{*requested};
    std::set<ValueOrigin> active{*requested};
    while (!stack.empty() && !types.diagnostic) {
      if (!types.charge(stack.back().second.size() + 1, span))
        return {};
      pending.reset();
      auto result = describe(stack.back());
      if (pending) {
        if (!active.insert(*pending).second) {
          types.fail("source.value-origin", "cyclic helper result", span);
          return {};
        }
        stack.push_back(std::move(*pending));
        continue;
      }
      auto type =
          types.projectedType(owner, body.values[stack.back().first].type,
                              stack.back().second, span);
      if (!type)
        return {};
      if (auto size = staticExtent(*type, 0)) {
        // Formation owns fixed extents. Never infer a relation from an
        // unchecked symbolic collection count, including through wrappers.
        result.shape = {};
        if (size->isClosed())
          result.shape.count =
              facts::Cardinality{size->closedValue(), facts::Precision::Exact};
      }
      values.emplace(stack.back(), std::move(result));
      active.erase(stack.back());
      stack.pop_back();
    }
    auto result = values[*requested];
    result.height = height;
    return result;
  }
};

const HelperResult *HelperResults::get(unsigned helper, unsigned result,
                                       ArrayRef<unsigned> path, Span span,
                                       unsigned depth) {
  if (depth > types.work.limits.callDepth) {
    types.fail("source.limit", "helper result call depth", span);
    return nullptr;
  }
  if (!types.charge(path.size() + 1, span))
    return nullptr;
  Key key{helper, result, path.vec()};
  if (auto found = memo.find(key); found != memo.end()) {
    if (depth + found->second.height > types.work.limits.callDepth) {
      types.fail("source.limit", "helper result call depth", span);
      return nullptr;
    }
    return &found->second;
  }
  if (helper >= declarations.size())
    return nullptr;
  const auto &callee = declarations[helper];
  if (callee.abstract || callee.kind != Declaration::Kind::Math ||
      !callee.body || result >= callee.body->results.size() ||
      !active.insert(key).second)
    return nullptr;
  auto leave = llvm::scope_exit([&] { active.erase(key); });
  auto [index, inserted] = origins.try_emplace(helper);
  if (inserted)
    index->second = std::make_unique<ValueOrigins>(types, *callee.body);
  auto summary =
      Extraction(*this, callee, *index->second, depth, span).run(result, path);
  if (types.diagnostic)
    return nullptr;
  return &memo.emplace(key, std::move(summary)).first->second;
}
} // namespace zkc::language::detail
