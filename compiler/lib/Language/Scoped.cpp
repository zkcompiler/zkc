#include "BodyCheck.h"
#include "CallableConstraints.h"
#include "Effects.h"
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
    if (found != scoped.end())
      return found->second;
    if (expr.binding) {
      fail("source.scoped", "expected a scoped parameter", expr.span);
      return {};
    }
    auto selected = selectCallable(checker.types, checker.output.declarations,
                                   inference->callees.at(id),
                                   inference->arguments.at(id), expr.span);
    if (!selected)
      return {};
    if (selected->signature.mode != signature.mode ||
        selected->signature.inputs != signature.inputs ||
        selected->signature.result != signature.result) {
      fail("source.scoped",
           "named callable signature differs from its receiver", expr.span);
      return {};
    }
    if (!effectsWithin(checker.types, selected->effects,
                       EffectSummary{signature.allowance}, expr.span)) {
      fail("source.effect", "named callable exceeds its receiving allowance",
           expr.span);
      return {};
    }
    if (!chargeSelectedCallable(checker.types, *selected, expr.span))
      return {};
    auto source = std::make_shared<ScopedSource>();
    source->owner = decl.id;
    source->expression = id;
    source->signature = signature;
    source->named = std::make_shared<const SelectedCallable>(*selected);
    unsigned witness = witnesses.sources.size();
    witnesses.sources.push_back(std::move(source));
    ScopedBinding binding{signature, {}, {}, {}, {}, expr.span, witness};
    binding.named =
        std::make_shared<const SelectedCallable>(std::move(*selected));
    unsigned index = body.scopedBindings.size();
    body.scopedBindings.push_back(std::move(binding));
    return index;
  }
  if (expr.kind != Expression::Kind::Lambda) {
    fail("source.scoped", "expected a scoped literal", expr.span);
    return {};
  }
  return scopedComputation(id, signature, depth);
}
std::optional<unsigned>
BodyChecker::scopedComputation(uint32_t id, const ScopedSignature &signature,
                               unsigned depth) {
  const auto &expr = syntax.expressions[id];
  const bool selected =
      expr.kind == Expression::Kind::And || expr.kind == Expression::Kind::Or;
  if (depth > checker.work.limits.expressionDepth ||
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
  unsigned sourceIndex = witnesses.sources.size();
  witnesses.sources.push_back(std::move(source));
  auto inputs = regionInputs(expr, selected);
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
  BodyChecker nested(checker, decl, syntax, *checked, callDepth + 1,
                     lexicalCallbackDepth + 1);
  nested.usageGuard = usageGuard;
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
    if (!type)
      return {};
    if (!checker.types.requireUsage(*type, Usage::Copy, span, &decl,
                                    "source.scoped-capture",
                                    "invariant captures require Copy")) {
      return {};
    }
    if (nested.math() && !nested.data(*type, span))
      return {};
    auto operand = capturePlace(capture, span);
    if (!operand)
      return {};
    if (product(*operand)) {
      fail("source.scoped-capture",
           "scoped computations cannot capture distributed products", span);
      return {};
    }
    if (!use(*operand, span))
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
  if (!inheritDomains(nested, inputs->domains, binding.descriptorCaptures))
    return {};
  for (auto capture : inputs->domains)
    computation->descriptorCaptures.push_back(capture.index);
  // Destructuring emits ordinary projections after every input is allocated.
  for (unsigned i = 0; i < parameters.size(); ++i)
    if (!nested.bindPattern(expr.payloads.front()[i], parameters[i]))
      return {};
  // The receiving Local signature supplies a literal's ordered root.
  // Implicit selected Math scopes never acquire Local action authority.
  if (!selected && syntax.layoutSyntax &&
      signature.mode == ScopedSignature::Mode::Local) {
    const auto &region = syntax.bodies[expr.regions.front()];
    if (region.results.size() == 1)
      nested.callbackRoot = region.results.front().second;
  }
  const auto span =
      selected ? expr.span : syntax.bodies[expr.regions.front()].span;
  auto result = selected ? nested.expression(id, signature.result, depth + 1)
                         : nested.tail(syntax.bodies[expr.regions.front()],
                                       signature.result, true);
  if (!result && (!checked->stopped || checker.types.diagnostic))
    return {};
  if (result) {
    if (!nested.use(*result, span))
      return {};
    checked->results.push_back(*result);
  }
  if (!nested.finish(span))
    return {};
  if (!effectsWithin(checker.types, checked->effects,
                     EffectSummary{signature.allowance}, expr.span)) {
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
  body.parameterizedSummary = true;
  auto dependencies = combine(operands, expr.span);
  if (!dependencies)
    return {};
  if (!checker.types.charge(1, expr.span))
    return {};
  auto source = uint32_t(witnesses.invocations.size());
  witnesses.invocations.push_back(std::make_shared<ScopedInvocationSource>(
      ScopedInvocationSource{decl.id, id, {}}));
  return emit(ScopedInvoke{found->second, std::move(operands), source},
              signature.result, ordered ? Components{} : *dependencies,
              expr.span);
}
bool Checker::retainScopedSources() {
  for (const auto &decl : output.declarations) {
    if ((!decl.body || !sources[decl.id.index]->resolved) &&
        decl.kind != Declaration::Kind::Protocol &&
        !(decl.kind == Declaration::Kind::View && !decl.abstract))
      continue;
    auto source = std::make_shared<ScopedSource>();
    source->owner = decl.id;
    source->expression = 0;
    source->syntax = retainSyntax(decl.id);
    if (!source->syntax)
      return false;
    if (auto families = witnesses.notations.find(decl.id.index);
        families != witnesses.notations.end())
      source->notationFamilies = families->second;
    if (auto enums = witnesses.enumTypes.find(decl.id.index);
        enums != witnesses.enumTypes.end())
      source->enumTypes = enums->second;
    if (auto maxima = witnesses.repeatMaxima.find(decl.id.index);
        maxima != witnesses.repeatMaxima.end())
      source->repeatMaxima = maxima->second;
    if (auto literals = witnesses.literals.find(decl.id.index);
        literals != witnesses.literals.end())
      source->literals = literals->second;
    if (auto captures = witnesses.controlSnapshots.find(decl.id.index);
        captures != witnesses.controlSnapshots.end())
      source->controlSnapshots = captures->second;
    output.bodySources.emplace(decl.id.index, std::move(source));
  }
  for (const auto &decl : output.declarations) {
    if (!types.charge(1, decl.span))
      return false;
    if (decl.scopedInputs.empty() && !decl.effectAllowance)
      continue;
    auto syntax = retainSyntax(decl.id);
    if (!syntax)
      return false;
    output.signatureSources.emplace(decl.id.index, std::move(syntax));
  }

  for (auto &source : witnesses.intrinsics) {
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.intrinsicCalls.push_back(std::move(source));
  }
  for (auto &source : witnesses.invocations) {
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.scopedInvocations.push_back(std::move(source));
  }
  for (auto &source : witnesses.sources) {
    if (auto families = witnesses.notations.find(source->owner.index);
        families != witnesses.notations.end())
      source->notationFamilies = families->second;
    if (auto enums = witnesses.enumTypes.find(source->owner.index);
        enums != witnesses.enumTypes.end())
      source->enumTypes = enums->second;
    if (auto maxima = witnesses.repeatMaxima.find(source->owner.index);
        maxima != witnesses.repeatMaxima.end())
      source->repeatMaxima = maxima->second;
    if (auto literals = witnesses.literals.find(source->owner.index);
        literals != witnesses.literals.end())
      source->literals = literals->second;
    if (auto captures = witnesses.controlSnapshots.find(source->owner.index);
        captures != witnesses.controlSnapshots.end())
      source->controlSnapshots = captures->second;
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.scopedSources.push_back(std::move(source));
  }
  for (auto &source : witnesses.calls) {
    source->syntax = retainSyntax(source->owner);
    if (!source->syntax)
      return false;
    output.scopedCalls.push_back(std::move(source));
  }
  return true;
}
} // namespace zkc::language::detail
