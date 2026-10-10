#include "OperatorInference.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
OperatorInference::OperatorInference(
    TypeInference &types, Semantics &semantics,
    const std::vector<Declaration> &declarations)
    : types(types), semantics(semantics), declarations(declarations) {}

void OperatorInference::add(uint32_t expression, Span span,
                            std::vector<TypeInference::Variable> inputs,
                            TypeInference::Variable result,
                            std::vector<Candidate> candidates) {
  choices.push_back(
      {expression, span, std::move(inputs), result, std::move(candidates)});
}

std::optional<CallableConstraints>
OperatorInference::apply(const Choice &choice, const Candidate &candidate,
                         bool *signatureFits) {
  if (signatureFits)
    *signatureFits = false;
  const auto &callee = declarations[candidate.target.declaration.index];
  auto application = instantiateCallable(types, semantics, callee,
                                         candidate.target, choice.span);
  if (semantics.diagnostic)
    return {};
  for (unsigned i = 0; i < candidate.arguments.size(); ++i)
    if (candidate.arguments[i])
      types.equal(application.parameters.at(callee.parameters[i].atom),
                  types.known(*candidate.arguments[i], choice.span),
                  choice.span);
  if (application.inputs.size() != choice.inputs.size() ||
      application.outputs.size() != 1) {
    semantics.fail("source.operator", "operator target signature differs",
                   choice.span, {candidate.binding});
    return {};
  }
  for (unsigned i = 0; i < choice.inputs.size(); ++i)
    types.equal(choice.inputs[i], application.inputs[i], choice.span);
  types.equal(choice.result, application.outputs.front(), choice.span);
  if (semantics.diagnostic)
    return {};
  if (signatureFits)
    *signatureFits = true;
  if (!types.solve(choice.span))
    return {};
  // Known static sorts participate in matching. Requirements do not.
  (void)callableArguments(types, semantics, callee, application, choice.span);
  return semantics.diagnostic ? std::nullopt
                              : std::optional(std::move(application));
}

bool OperatorInference::coherence(const Choice &choice,
                                  const Candidate &selected) {
  std::vector<Type> inputs;
  for (auto input : choice.inputs) {
    auto type = types.get(input, choice.span);
    if (!type)
      return false;
    inputs.push_back(std::move(*type));
  }
  for (const auto &candidate : choice.candidates) {
    // The environment has already deduplicated canonical binding identities.
    if (&candidate == &selected)
      continue;
    TypeInference probe(semantics);
    const auto &callee = declarations[candidate.target.declaration.index];
    auto application = instantiateCallable(
        probe, semantics, callee, candidate.target, choice.span, false);
    if (semantics.diagnostic)
      return false;
    if (application.inputs.size() != inputs.size())
      return semantics.fail("source.operator", "operator input count differs",
                            choice.span, {candidate.binding});
    for (unsigned i = 0; i < candidate.arguments.size(); ++i)
      if (candidate.arguments[i])
        probe.equal(application.parameters.at(callee.parameters[i].atom),
                    probe.known(*candidate.arguments[i], choice.span),
                    choice.span);
    for (unsigned i = 0; i < inputs.size(); ++i)
      probe.equal(application.inputs[i], probe.known(inputs[i], choice.span),
                  choice.span);
    probe.solve(choice.span);
    (void)callableArguments(probe, semantics, callee, application, choice.span);
    if (semantics.diagnostic) {
      if (semantics.diagnostic->code == "source.limit")
        return false;
      semantics.diagnostic.reset();
      continue;
    }
    // An unbound associated input is still a possible competitor. Result
    // context, effects or capability evidence cannot dismiss it.
    return semantics.fail(
        "source.operator",
        "distinct operator targets accept the same operand types; use a "
        "named call or a local operator binding",
        choice.span, {selected.binding, candidate.binding});
  }
  return true;
}

bool OperatorInference::propagate(Span span) {
  std::map<unsigned, Chosen> chosen;
  if (!types.solve(span))
    return false;
  if (propagate(chosen))
    return true;
  if (!semantics.diagnostic)
    semantics.fail("source.operator",
                   "no operator target matches the expression", span);
  return false;
}

bool OperatorInference::propagate(std::map<unsigned, Chosen> &chosen) {
  bool progress;
  do {
    progress = false;
    for (unsigned i = 0; i < choices.size(); ++i) {
      if (chosen.count(i))
        continue;
      const auto &choice = choices[i];
      auto checkpoint = types.checkpoint(choice.span);
      if (!checkpoint)
        return false;
      std::vector<unsigned> viable;
      std::optional<Diagnostic> structuralFailure;
      unsigned matchingSignatures = 0;
      for (unsigned j = 0; j < choice.candidates.size(); ++j) {
        bool signatureFits = false;
        auto application = apply(choice, choice.candidates[j], &signatureFits);
        matchingSignatures += signatureFits;
        if (application)
          viable.push_back(j);
        if (semantics.diagnostic &&
            semantics.diagnostic->code == "source.limit")
          return false;
        if (signatureFits && semantics.diagnostic)
          structuralFailure = semantics.diagnostic;
        semantics.diagnostic.reset();
        if (!types.restore(*checkpoint, choice.span))
          return false;
      }
      if (viable.empty()) {
        // Preserve a structural explanation when the signature alternatives
        // have all failed. A surrounding branch may still refute this path.
        if (matchingSignatures == 1 && structuralFailure)
          semantics.diagnostic = std::move(structuralFailure);
        return false;
      }
      if (viable.size() == 1) {
        auto application = apply(choice, choice.candidates[viable.front()]);
        if (!application)
          return false;
        chosen.emplace(i, Chosen{viable.front(), std::move(*application)});
        progress = true;
      }
    }
  } while (progress);
  return true;
}

std::optional<std::map<uint32_t, OperatorInference::Selection>>
OperatorInference::solve(Span span, const std::function<bool()> &complete) {
  if (!types.solve(span))
    return {};
  if (choices.empty())
    return std::map<uint32_t, Selection>{};
  llvm::sort(choices, [](const Choice &a, const Choice &b) {
    return a.expression < b.expression;
  });
  std::map<unsigned, Chosen> chosen;
  auto baseline = types.checkpoint(span);
  if (!baseline)
    return {};
  std::map<unsigned, Chosen> solutionCalls;
  bool unresolved = false, ambiguous = false;
  unsigned solutions = 0;
  std::function<void(unsigned)> search = [&](unsigned depth) {
    if (semantics.diagnostic || solutions > 1 || ambiguous)
      return;
    if (!semantics.charge(1, span))
      return;
    if (depth > semantics.work.limits.expressionDepth) {
      semantics.fail("source.limit", "operator inference branch depth exceeded",
                     span);
      return;
    }
    if (!propagate(chosen))
      return;
    if (chosen.size() == choices.size()) {
      bool settled = complete();
      for (const auto &[i, selected] : chosen) {
        const auto &choice = choices[i];
        const auto &callee =
            declarations[selected.application.target.declaration.index];
        settled &= callableArguments(types, semantics, callee,
                                     selected.application, choice.span)
                       .has_value();
        settled &= types.get(choice.result, choice.span).has_value();
        for (auto input : choice.inputs)
          settled &= types.get(input, choice.span).has_value();
      }
      if (semantics.diagnostic)
        return;
      if (!settled) {
        unresolved = true;
        return;
      }
      for (const auto &[i, selected] : chosen)
        if (!coherence(choices[i], choices[i].candidates[selected.candidate])) {
          ambiguous = semantics.diagnostic &&
                      semantics.diagnostic->code == "source.operator";
          return;
        }
      ++solutions;
      if (solutions == 1) {
        solutionCalls = chosen;
      }
      return;
    }
    unsigned next = 0;
    while (chosen.count(next))
      ++next;
    auto checkpoint = types.checkpoint(span);
    if (!checkpoint)
      return;
    auto prefix = chosen;
    const auto &choice = choices[next];
    for (unsigned candidate = 0; candidate < choice.candidates.size();
         ++candidate) {
      auto application = apply(choice, choice.candidates[candidate]);
      if (application) {
        chosen.emplace(next, Chosen{candidate, std::move(*application)});
        search(depth + 1);
      }
      if ((semantics.diagnostic &&
           semantics.diagnostic->code == "source.limit") ||
          ambiguous || solutions > 1)
        return;
      semantics.diagnostic.reset();
      if (!types.restore(*checkpoint, span))
        return;
      chosen = prefix;
    }
  };
  search(1);
  if (semantics.diagnostic)
    return {};
  if (solutions > 1) {
    semantics.fail("source.operator",
                   "operator expression has multiple type solutions", span);
    return {};
  }
  if (unresolved || !solutions) {
    semantics.fail(unresolved ? "source.inference" : "source.operator",
                   unresolved
                       ? "operator expression needs more type information"
                       : "no operator target matches the expression",
                   span);
    return {};
  }
  if (!types.restore(*baseline, span))
    return {};
  std::map<uint32_t, Selection> result;
  for (auto &[i, selected] : solutionCalls) {
    const auto &choice = choices[i];
    auto application = apply(choice, choice.candidates[selected.candidate]);
    if (!application)
      return {};
    result.emplace(choice.expression,
                   Selection{std::move(*application),
                             choice.candidates[selected.candidate].binding});
  }
  if (!types.solve(span))
    return {};
  choices.clear();
  return result;
}
} // namespace zkc::language::detail
