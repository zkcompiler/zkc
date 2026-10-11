#include "FiniteContracts.h"
#include "ValueOrigins.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct Item {
  unsigned domain;
  std::vector<unsigned> path;
};
using Facts = std::vector<std::optional<Item>>;
using Restrictions = std::vector<std::optional<unsigned>>;

// A generic declaration is checked with distinct abstract domain identities.
// Literal bodies are checked at their binding occurrence, after all eager
// arguments have been elaborated. This makes named argument order irrelevant
// to checking without changing when captures or ordinary values are evaluated.
class ContractCheck {
  Semantics &types;
  ArrayRef<Declaration> declarations;
  unsigned nextDomain = 0;
  struct Context {
    const Body &body;
    Facts inputs;
    Restrictions scoped;
    std::vector<unsigned> domains;
    ValueOrigins origins;
    Context(Semantics &types, const Body &body, Facts inputs,
            Restrictions scoped)
        : body(body), inputs(std::move(inputs)), scoped(std::move(scoped)),
          origins(types, body) {}
  };
  bool refuse(Span span, StringRef message) {
    return types.fail("source.scoped-domain", message, span);
  }
  bool bounded(unsigned depth, Span span) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "finite contract checking depth", span);
    return types.charge(1, span);
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
  bool restriction(Context &context, unsigned index,
                   std::optional<unsigned> &result, Span span) {
    if (index >= context.body.scopedBindings.size())
      return refuse(span, "scoped binding is outside its body");
    const auto &binding = context.body.scopedBindings[index];
    if (!binding.parameter || *binding.parameter >= context.scoped.size())
      return refuse(span, "scoped invocation requires a bound formal");
    result = context.scoped[*binding.parameter];
    return true;
  }
  bool domain(Context &context, unsigned index, unsigned &result, Span span) {
    if (index >= context.domains.size())
      return refuse(span, "finite domain is outside its body");
    result = context.domains[index];
    return true;
  }
  bool callback(Context &context, unsigned index,
                std::optional<unsigned> expected, unsigned depth, Span span) {
    if (!bounded(depth, span) || index >= context.body.scopedBindings.size())
      return types.diagnostic ? false : refuse(span, "missing scoped binding");
    const auto &binding = context.body.scopedBindings[index];
    if (binding.parameter) {
      std::optional<unsigned> actual;
      if (!restriction(context, index, actual, span))
        return false;
      return !actual || actual == expected ||
             refuse(span, "restricted callback requires the same item domain");
    }
    if (!binding.computation || !binding.computation->body)
      return refuse(span, "missing scoped computation");
    const auto &computation = *binding.computation;
    const auto &nested = *computation.body;
    unsigned explicitInputs = computation.signature.inputs.size();
    if (nested.inputs != explicitInputs + binding.captures.size() ||
        (expected && !explicitInputs))
      return refuse(span, "scoped input coverage differs");
    if (!types.charge(nested.inputs + binding.scopedCaptures.size() +
                          binding.domainCaptures.size(),
                      span))
      return false;
    Facts inputs(nested.inputs);
    if (expected)
      inputs[explicitInputs - 1] = Item{*expected, {}};
    for (unsigned i = 0; i < binding.captures.size(); ++i)
      if (!fact(context, binding.captures[i], inputs[explicitInputs + i], span))
        return false;
    Restrictions selected(binding.scopedCaptures.size());
    for (unsigned i = 0; i < selected.size(); ++i)
      if (!restriction(context, binding.scopedCaptures[i], selected[i], span))
        return false;
    std::vector<unsigned> domains(binding.domainCaptures.size());
    for (unsigned i = 0; i < domains.size(); ++i)
      if (!domain(context, binding.domainCaptures[i], domains[i], span))
        return false;
    return body(nested, std::move(inputs), std::move(selected), domains,
                depth + 1);
  }
  bool call(Context &context, const HelperCall &call, unsigned depth,
            Span span) {
    if (call.callee.index >= declarations.size())
      return refuse(span, "unknown finite call target");
    const auto &callee = declarations[call.callee.index];
    if (call.scopedArguments.size() != callee.scopedInputs.size() ||
        call.domainArguments.size() != callee.domainInputs.size())
      return refuse(span, "static call argument coverage differs");
    for (unsigned i = 0; i < call.scopedArguments.size(); ++i) {
      std::optional<unsigned> expected;
      if (auto formal = callee.scopedInputs[i].signature.itemDomain) {
        unsigned selected;
        if (*formal >= call.domainArguments.size() ||
            !domain(context, call.domainArguments[*formal], selected, span))
          return types.diagnostic ? false : refuse(span, "invalid item domain");
        expected = selected;
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
      unsigned prefix = region->inputs - forwarded;
      for (unsigned i = 0; i < forwarded; ++i) {
        // A carried value is a fresh successor even on a zero-trip path.
        if (loop && i < control.carried)
          continue;
        if (!fact(context, control.operands[skipped + i], inputs[prefix + i],
                  span))
          return false;
      }
      if (!body(*region, std::move(inputs), context.scoped, domains, depth + 1))
        return false;
    }
    return true;
  }
  bool body(const Body &source, Facts inputs, Restrictions scoped,
            ArrayRef<unsigned> environment, unsigned depth) {
    if (!bounded(depth, {}) ||
        !types.charge(source.values.size() + source.domainBindings.size() +
                          source.scopedBindings.size() +
                          source.operations.size(),
                      {}))
      return false;
    if (inputs.size() != source.inputs || source.inputs > source.values.size())
      return refuse({}, "body input coverage differs");
    Context context(types, source, std::move(inputs), std::move(scoped));
    for (const auto &binding : source.domainBindings) {
      if (binding.parameter) {
        if (*binding.parameter >= environment.size())
          return refuse(binding.span, "missing finite domain environment");
        context.domains.push_back(environment[*binding.parameter]);
      } else
        context.domains.push_back(nextDomain++);
    }
    for (const auto &op : source.operations) {
      if (!bounded(depth, op.span))
        return false;
      if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
        std::optional<unsigned> required;
        if (!restriction(context, invoke->binding, required, op.span))
          return false;
        if (required) {
          std::optional<Item> actual;
          if (invoke->operands.empty() ||
              !fact(context, invoke->operands.back(), actual, op.span))
            return types.diagnostic ? false : refuse(op.span, "missing item");
          if (!actual || !actual->path.empty() || actual->domain != *required)
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
            !callback(context, finite->body, selected, depth + 1, op.span) ||
            (finite->predicate && !callback(context, *finite->predicate,
                                            selected, depth + 1, op.span)))
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
        for (unsigned i = 0; i < repeat->captures.size(); ++i)
          if (!fact(context, repeat->captures[i],
                    nested[1 + repeat->carried.size() + i], op.span))
            return false;
        if (!body(*repeat->region, std::move(nested), {}, {}, depth + 1))
          return false;
      }
    }
    return true;
  }

public:
  ContractCheck(Semantics &types, ArrayRef<Declaration> declarations)
      : types(types), declarations(declarations) {}
  bool run(const Declaration &decl, const Body &source) {
    if (!types.charge(source.inputs + decl.domainInputs.size() +
                          decl.scopedInputs.size(),
                      decl.span))
      return false;
    std::vector<unsigned> domains;
    for (unsigned i = 0; i < decl.domainInputs.size(); ++i)
      domains.push_back(nextDomain++);
    Restrictions selected;
    for (const auto &parameter : decl.scopedInputs) {
      auto formal = parameter.signature.itemDomain;
      if (formal && *formal >= domains.size())
        return refuse(parameter.span, "invalid declared item domain");
      selected.push_back(formal ? std::optional<unsigned>(domains[*formal])
                                : std::nullopt);
    }
    return body(source, Facts(source.inputs), std::move(selected), domains, 1);
  }
};
} // namespace
bool checkFiniteContracts(Semantics &types, ArrayRef<Declaration> declarations,
                          const Declaration &decl, const Body &body) {
  return ContractCheck(types, declarations).run(decl, body);
}
} // namespace zkc::language::detail
