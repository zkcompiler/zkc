#include "BodyCheck.h"
#include "ScopedWitness.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::addScoped(BindingId binding, const ScopedSignature &signature,
                            Span span) {
  if (!checker.types.charge(signature.inputs.size() + 1, span))
    return false;
  unsigned index = body.scopedBindings.size();
  scoped.emplace(binding, index);
  body.scopedBindings.push_back({signature, index, {}, {}, {}, span, {}});
  return true;
}
bool BodyChecker::inheritScoped(BodyChecker &nested) {
  // Lexical scoped names are parameters; literal arguments never bind names.
  for (const auto &[binding, index] : scoped)
    if (!nested.addScoped(binding, body.scopedBindings[index].signature,
                          body.scopedBindings[index].span))
      return false;
  return true;
}
std::optional<unsigned>
BodyChecker::scopedArgument(uint32_t id, const ScopedSignature &signature,
                            unsigned depth) {
  const auto &expr = syntax.expressions[id];
  if (expr.kind == Expression::Kind::Name) {
    auto found = expr.binding ? scoped.find(*expr.binding) : scoped.end();
    if (found == scoped.end()) {
      fail("source.scoped", "expected a scoped parameter", expr.span);
      return {};
    }
    return found->second;
  }
  if (expr.kind != Expression::Kind::Lambda ||
      depth > checker.work.limits.expressionDepth ||
      callDepth + 1 > checker.work.limits.callDepth) {
    fail("source.limit", "scoped computation depth exceeded", expr.span);
    return {};
  }
  auto source = std::make_shared<ScopedSource>();
  source->owner = decl.id;
  source->expression = id;
  source->signature = signature;
  source->scoped = scoped;
  source->domains = domains;
  for (const auto &[name, state] : bindings) {
    if (!checker.types.charge(state.pieces.size() + 1, expr.span) ||
        !checker.types.chargeType(state.type, expr.span))
      return {};
    source->environment.emplace(
        name, ScopedSource::Place{state.type, state.value, state.pieces});
  }
  unsigned sourceIndex = checker.scopedSources.size();
  checker.scopedSources.push_back(std::move(source));
  auto inputs = regionInputs(expr);
  if (!inputs)
    return {};
  if (!inputs->writes.empty() || !inputs->services.empty()) {
    fail("source.scoped-capture",
         "scoped computations cannot write outer bindings or capture managed "
         "services",
         expr.span);
    return {};
  }
  auto computation = std::make_shared<ScopedComputation>();
  computation->lexicalOwner = decl.id;
  computation->expression = id;
  computation->signature = signature;
  auto checked = std::make_shared<Body>();
  checked->mode = signature.mode == ScopedSignature::Mode::Math
                      ? Body::Mode::Math
                      : Body::Mode::Local;
  BodyChecker nested(checker, decl, syntax, *checked, callDepth + 1);
  nested.inference = inference;
  nested.retainExpressionValues = true;
  ScopedBinding binding{signature, {},        computation, {},
                        {},        expr.span, sourceIndex};
  std::vector<ValueId> parameters;
  for (unsigned i = 0; i < signature.inputs.size(); ++i) {
    if (nested.math() && !nested.data(signature.inputs[i], expr.span))
      return {};
    auto value = nested.input(signature.inputs[i],
                              nested.math() ? std::vector<unsigned>{i}
                                            : std::vector<unsigned>{},
                              expr.span);
    if (!value)
      return {};
    parameters.push_back(*value);
  }
  std::vector<FreePlace> captures(inputs->places.begin(), inputs->places.end());
  std::stable_sort(captures.begin(), captures.end(),
                   [&](const auto &a, const auto &b) {
                     return inputs->occurrences.at(a).begin <
                            inputs->occurrences.at(b).begin;
                   });
  for (const auto &capture : captures) {
    auto span = inputs->occurrences.at(capture);
    auto type =
        projected(bindings.at(capture.binding).type, capture.path, span);
    auto permissions =
        type ? checker.types.permissions(*type, span, &decl) : std::nullopt;
    if (!permissions)
      return {};
    if (!permissions->copy || !permissions->drop) {
      fail("source.scoped-capture", "invariant captures require Copy and Drop",
           span);
      return {};
    }
    if (nested.math() && !nested.data(*type, span))
      return {};
    auto operand = capturePlace(capture, span);
    if (!operand || !use(*operand, span))
      return {};
    binding.captures.push_back(*operand);
    computation->captures.push_back(
        {capture.binding.index, capture.path, *type, span});
    auto input =
        nested.input(*type,
                     nested.math() ? std::vector<unsigned>{checked->inputs}
                                   : std::vector<unsigned>{},
                     span);
    if (!input)
      return {};
    auto [it, inserted] = nested.bindings.try_emplace(
        capture.binding,
        BindingState{bindings.at(capture.binding).type, {}, {}, {}});
    if (capture.path.empty())
      it->second.value = *input;
    else
      it->second.pieces.emplace_back(capture.path, *input);
  }
  for (auto capture : inputs->scoped) {
    auto index = scoped.at(capture);
    const auto &captured = body.scopedBindings[index];
    if (!nested.addScoped(capture, captured.signature, captured.span))
      return {};
    binding.scopedCaptures.push_back(index);
    computation->scopedCaptures.push_back(capture.index);
  }
  if (!inheritDomains(nested, inputs->domains, binding.domainCaptures))
    return {};
  for (auto capture : inputs->domains)
    computation->domainCaptures.push_back(capture.index);
  // Destructuring emits ordinary projections after every input is allocated.
  for (unsigned i = 0; i < parameters.size(); ++i)
    if (!nested.bindPattern(expr.payloads.front()[i], parameters[i]))
      return {};
  const auto &region = syntax.bodies[expr.regions.front()];
  auto result = nested.tail(region, signature.result, true);
  if (!result && (!checked->stopped || checker.types.diagnostic))
    return {};
  if (result) {
    if (!nested.use(*result, region.span))
      return {};
    checked->results.push_back(*result);
  }
  if (!nested.finish(region.span))
    return {};
  if ((checked->mayStop && !signature.allowance.mayStop) ||
      (checked->opaque && !signature.allowance.opaque)) {
    fail("source.effect", "scoped body exceeds its signature allowance",
         expr.span);
    return {};
  }
  computation->body = std::move(checked);
  auto index = unsigned(body.scopedBindings.size());
  body.scopedBindings.push_back(std::move(binding));
  return index;
}
std::optional<ValueId> BodyChecker::invokeScoped(uint32_t id, unsigned depth) {
  const auto &expr = syntax.expressions[id];
  auto found = scoped.find(*expr.binding);
  if (found == scoped.end()) {
    fail("source.scoped", "lexical binding is not callable", expr.span);
    return {};
  }
  const auto signature = body.scopedBindings[found->second].signature;
  bool ordered = signature.mode == ScopedSignature::Mode::Local;
  if (ordered && !local()) {
    fail("source.mode", "Local scoped invocation requires Local mode",
         expr.span);
    return {};
  }
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto value = expression(expr.children[i], signature.inputs[i], depth + 1);
    if (!value || !use(*value, expr.span) ||
        !checker.types.charge(1, expr.span))
      return {};
    body.expressionValues.insert_or_assign(expr.children[i], *value);
    operands.push_back(*value);
  }
  body.mayStop |= signature.allowance.mayStop;
  body.opaque |= signature.allowance.opaque;
  body.parameterizedSummary = true;
  auto dependencies = combine(operands, expr.span);
  if (!dependencies)
    return {};
  if (!checker.types.charge(1, expr.span))
    return {};
  auto source = uint32_t(checker.scopedInvocations.size());
  checker.scopedInvocations.push_back(std::make_shared<ScopedInvocationSource>(
      ScopedInvocationSource{decl.id, id, {}}));
  return emit(ScopedInvoke{found->second, std::move(operands), source},
              signature.result, ordered ? Components{} : *dependencies,
              expr.span);
}
bool Checker::retainScopedSources() {
  for (auto &source : scopedInvocations) {
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.scopedInvocations.push_back(std::move(source));
  }
  for (auto &source : scopedSources) {
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.scopedSources.push_back(std::move(source));
  }
  for (auto &source : scopedCalls) {
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.scopedCalls.push_back(std::move(source));
  }
  return true;
}
} // namespace zkc::language::detail
