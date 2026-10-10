#include "BindingWitness.h"
#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool sameOperands(ArrayRef<ValueId> a, ArrayRef<ValueId> b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(),
                    [](ValueId x, ValueId y) { return x.index == y.index; });
}
bool sameTarget(const CallableReference &a, const CallableReference &b) {
  return a.declaration.index == b.declaration.index &&
         a.component == b.component;
}
bool sameSpan(Span a, Span b) {
  return a.module.index == b.module.index && a.begin == b.begin &&
         a.end == b.end;
}
bool checkNotationArity(Semantics &types, const NotationDescriptor &notation,
                        size_t inputs, Span span) {
  using Position = NotationDescriptor::Position;
  bool valid = false;
  switch (notation.position) {
  case Position::Reduction:
  case Position::Prefix:
  case Position::Postfix:
    valid = notation.arity == 1;
    break;
  case Position::Infix:
    valid = notation.arity == 2;
    break;
  case Position::Delimited:
    if (notation.arity > types.work.limits.notationHoles)
      return types.fail("source.limit", "notation hole limit exceeded", span);
    valid = notation.arity > 0;
    break;
  }
  return (valid && notation.arity == inputs) ||
         types.fail("source.binding-witness", "notation input count differs",
                    span);
}
/// Ground operand matching keeps unknown forward equations as competitors.
class GroundMatch {
  Semantics &types;
  const Declaration &callee;
  Span span;
  Substitution bound;
  std::set<std::string> parameters;
  bool unresolved = false;
  bool ready(const Type &value) const {
    if (parameters.count(value.domain) && !bound.count(value.domain))
      return false;
    if (value.kind == Type::Kind::Natural || value.kind == Type::Kind::Array)
      for (const auto &[factors, coefficient] : value.dimension.terms()) {
        (void)coefficient;
        for (const auto &factor : factors)
          if (parameters.count(factor.name) && !bound.count(factor.name))
            return false;
      }
    return llvm::all_of(value.arguments,
                        [&](const Type &arg) { return ready(arg); });
  }
  bool match(const Type &pattern, const Type &actual, unsigned depth) {
    if (depth > types.work.limits.typeDepth)
      return types.fail("source.limit", "binding witness type depth exceeded",
                        span);
    if (!types.chargeType(pattern, span) || !types.chargeType(actual, span))
      return false;
    // Only a bare formal is injective. Composite naturals and associations
    // are compared after their inputs are known.
    bool bare = pattern.symbolic && parameters.count(pattern.domain) &&
                (pattern.kind != Type::Kind::Natural ||
                 pattern.dimension == cantFail(Natural::atom(pattern.domain)));
    if (bare) {
      auto parameter =
          llvm::find_if(callee.parameters, [&](const Parameter &p) {
            return p.atom == pattern.domain;
          });
      using S = Parameter::Sort;
      if ((parameter->sort == S::Domain &&
           domainSort(actual) != parameter->domainSort) ||
          (parameter->sort == S::Natural &&
           actual.kind != Type::Kind::Natural) ||
          (parameter->sort == S::Asset &&
           assetSort(actual) != parameter->domainSort) ||
          (parameter->sort == S::Component &&
           actual.kind != Type::Kind::Component) ||
          (parameter->sort == S::Type &&
           (!valueType(actual) || actual.kind == Type::Kind::Formal)))
        return false;
      auto found = bound.find(pattern.domain);
      if (found != bound.end())
        return found->second == actual;
      bound.emplace(pattern.domain, actual);
      return true;
    }
    if (pattern.kind == Type::Kind::Natural ||
        pattern.kind == Type::Kind::Associated ||
        (!domainSort(pattern).empty() && !pattern.arguments.empty())) {
      if (!ready(pattern)) {
        unresolved = true;
        return true;
      }
      auto value = types.substitute(pattern, bound, span);
      return value && *value == actual;
    }
    if (pattern.kind != actual.kind || pattern.domain != actual.domain ||
        pattern.symbolic != actual.symbolic ||
        pattern.arguments.size() != actual.arguments.size())
      return false;
    if (pattern.kind == Type::Kind::Array) {
      Type expected(Type::Kind::Natural), provided(Type::Kind::Natural);
      expected.dimension = pattern.dimension;
      provided.dimension = actual.dimension;
      const auto &terms = pattern.dimension.terms();
      if (terms.size() == 1 && terms.begin()->second == 1 &&
          terms.begin()->first.size() == 1 &&
          terms.begin()->first.front().kind == Natural::Factor::Kind::Atom) {
        expected.domain = terms.begin()->first.front().name;
        expected.symbolic = true;
      }
      if (!match(expected, provided, depth + 1))
        return false;
    }
    for (unsigned i = 0; i < pattern.arguments.size(); ++i)
      if (!match(pattern.arguments[i], actual.arguments[i], depth + 1))
        return false;
    return true;
  }

public:
  GroundMatch(Semantics &types, const Declaration &callee, Span span)
      : types(types), callee(callee), span(span) {
    for (const auto &parameter : callee.parameters)
      parameters.insert(parameter.atom);
  }
  bool accepts(const OperatorBinding &binding, ArrayRef<Type> inputs) {
    auto excluded = [&] {
      // Signature contradictions exclude a competitor; exhausted checking
      // resources must still fail the entire witness check.
      if (types.diagnostic && types.diagnostic->code != "source.limit")
        types.diagnostic.reset();
      return false;
    };
    if (binding.arguments.size() != callee.parameters.size() ||
        inputs.size() != callee.inputs.size())
      return false;
    for (unsigned i = 0; i < binding.arguments.size(); ++i)
      if (binding.arguments[i])
        bound.emplace(callee.parameters[i].atom, *binding.arguments[i]);
    if (binding.target.component) {
      auto inherited = types.boundMemberSubstitution(
          callee, *binding.target.component, span);
      if (!inherited)
        return excluded();
      for (const auto &[name, value] : *inherited)
        bound.insert_or_assign(name, value);
    }
    size_t previous;
    do {
      previous = bound.size();
      unresolved = false;
      for (unsigned i = 0; i < inputs.size(); ++i)
        if (!match(callee.inputs[i].type, inputs[i], 1))
          return excluded();
    } while (unresolved && bound.size() != previous);
    std::vector<std::optional<Type>> arguments;
    for (const auto &parameter : callee.parameters) {
      auto found = bound.find(parameter.atom);
      arguments.push_back(found == bound.end() ? std::nullopt
                                               : std::optional(found->second));
    }
    if (!types.checkKnownArgumentSorts(callee, arguments, span, bound))
      return excluded();
    // Incomplete associated/static matching remains potentially applicable.
    return true;
  }
};
} // namespace
bool checkNotationOccurrence(Semantics &types, const Expression &expr,
                             const NotationEnvironment &environment) {
  auto refuse = [&] {
    return types.fail("source.binding-witness",
                      "notation occurrence differs from its lexical syntax",
                      expr.span);
  };
  if (expr.kind != Expression::Kind::NotationCall || !expr.notation)
    return refuse();
  if (!types.charge(expr.notation->symbol.size() +
                        expr.notation->closing.size() + 1,
                    expr.span))
    return false;
  const auto found = environment.find(expr.notation->key());
  if (found == environment.end() || !found->second.descriptor ||
      *found->second.descriptor != *expr.notation || !expr.arguments.empty() ||
      !expr.staticLabels.empty() || !expr.callLabels.empty() || expr.roles)
    return refuse();
  return checkNotationArity(types, *found->second.descriptor,
                            expr.children.size(), expr.span);
}

std::optional<std::vector<OperatorBinding>>
Checker::operatorWitnessFamily(const Declaration &decl,
                               const SyntaxDeclaration &source,
                               uint32_t expression) {
  const auto &expr = source.expressions[expression];
  const NotationEnvironment *environment = nullptr;
  if (expr.scope && *expr.scope < source.bodies.size())
    environment = source.bodies[*expr.scope].notationEnvironment.get();
  else if (!expr.scope && decl.module.index < notationEnvironments.size())
    environment = notationEnvironments[decl.module.index].get();
  if (!environment) {
    types.fail("source.binding-witness",
               "notation scope has no syntax environment", expr.span);
    return {};
  }
  if (!checkNotationOccurrence(types, expr, *environment))
    return {};
  const auto descriptorKey = expr.notation->key();
  // Reconstruct the family from the checked lexical environment, without
  // using operatorCandidates or any candidate list produced by inference.
  std::map<std::string, OperatorBinding> family;
  auto include = [&](const OperatorBinding &binding) {
    if (!binding.notation)
      return types.fail("source.binding-witness",
                        "notation binding has no descriptor", expr.span);
    if (!types.charge(binding.notation->symbol.size() +
                          binding.notation->closing.size() + 1,
                      expr.span))
      return false;
    if (binding.notation->key() != descriptorKey)
      return true;
    if (*binding.notation != *expr.notation ||
        binding.symbol != expr.notation->symbol ||
        binding.target.declaration.index >= output.declarations.size())
      return types.fail("source.binding-witness",
                        "notation binding shape differs", expr.span);
    auto key = operatorBindingKey(binding, output.declarations);
    if (!types.charge(key.size() + 1, expr.span))
      return false;
    family.try_emplace(std::move(key), binding);
    return true;
  };
  auto scope = expr.scope;
  unsigned depth = 0;
  while (scope && family.empty()) {
    if (*scope >= source.bodies.size() ||
        ++depth > work.limits.expressionDepth) {
      types.fail("source.binding-witness", "invalid notation scope", expr.span);
      return {};
    }
    const auto &region = source.bodies[*scope];
    if (!types.charge(region.resolvedOperators.size() + 1, expr.span))
      return {};
    for (const auto &binding : region.resolvedOperators)
      if (!include(binding))
        return {};
    scope = region.parent;
  }
  if (family.empty()) {
    if (!types.charge(visibleOperators[decl.module.index].size() + 1,
                      expr.span))
      return {};
    for (auto site : visibleOperators[decl.module.index])
      if (!include(moduleOperators.at(site)))
        return {};
  }
  std::vector<OperatorBinding> result;
  for (auto &[key, binding] : family)
    result.push_back(std::move(binding));
  return result;
}

bool checkCallInputMapping(Semantics &types, ArrayRef<unsigned> mapping,
                           unsigned inputs, Span span) {
  if (!types.charge(mapping.size() + 1, span))
    return false;
  auto refuse = [&] {
    return types.fail("source.binding-witness",
                      "call input mapping is not a permutation", span);
  };
  if (mapping.size() != inputs)
    return refuse();
  std::vector<bool> seen(inputs);
  for (auto input : mapping) {
    if (input >= inputs || seen[input])
      return refuse();
    seen[input] = true;
  }
  return true;
}

bool checkOperatorOperands(Semantics &types, const NotationDescriptor &notation,
                           const CallBinding &witness,
                           ArrayRef<unsigned> parameterOrder,
                           ArrayRef<ValueId> authoredOperands, Span span) {
  if (!types.charge(parameterOrder.size() + authoredOperands.size() + 1,
                    span) ||
      !checkNotationArity(types, notation, authoredOperands.size(), span))
    return false;
  if (!witness.notation || *witness.notation != notation ||
      parameterOrder.size() != authoredOperands.size() ||
      !sameOperands(witness.operands, authoredOperands))
    return types.fail("source.binding-witness",
                      "operator operands differ from authored order", span);
  for (unsigned i = 0; i < parameterOrder.size(); ++i)
    if (parameterOrder[i] != i)
      return types.fail("source.binding-witness",
                        "operator operands differ from authored order", span);
  return true;
}

bool checkOperatorWitness(Semantics &types, ArrayRef<Declaration> declarations,
                          ArrayRef<OperatorBinding> expected,
                          const NotationDescriptor &notation,
                          const CallBinding &witness, ArrayRef<Type> inputs,
                          const Type &output, Span span) {
  auto refuse = [&] {
    return types.fail(
        "source.binding-witness",
        "operator binding evidence differs from its definition environment",
        span);
  };
  if (witness.target.declaration.index >= declarations.size() ||
      witness.family.size() != expected.size() || !witness.origin ||
      !witness.notation || *witness.notation != notation ||
      witness.symbol != notation.symbol ||
      witness.operands.size() != inputs.size())
    return refuse();
  if (!checkNotationArity(types, notation, inputs.size(), span))
    return false;
  const auto &selected = declarations[witness.target.declaration.index];
  if (witness.arguments.size() != selected.parameters.size() ||
      selected.inputs.size() != inputs.size() || selected.outputs.size() != 1 ||
      (selected.kind != Declaration::Kind::Math &&
       selected.kind != Declaration::Kind::Local) ||
      (notation.position == NotationDescriptor::Position::Infix &&
       notation.symbol == "==" && selected.outputs.front().type != Type{}))
    return refuse();
  auto subst = types.substitution(selected, witness.arguments);
  if (witness.target.component && selected.parent)
    subst.emplace("self:" + declarations[selected.parent->index].qualifiedName,
                  *witness.target.component);
  bool found = false;
  for (unsigned i = 0; i < expected.size(); ++i) {
    const auto &binding = expected[i];
    if (binding.target.declaration.index >= declarations.size() ||
        !binding.notation || *binding.notation != notation ||
        binding.arguments.size() !=
            declarations[binding.target.declaration.index].parameters.size())
      return refuse();
    const auto &callee = declarations[binding.target.declaration.index];
    if (callee.inputs.size() != inputs.size() || callee.outputs.size() != 1 ||
        (callee.kind != Declaration::Kind::Math &&
         callee.kind != Declaration::Kind::Local))
      return refuse();
    if (!types.charge(witness.family[i].size() + 1, span))
      return false;
    if (witness.family[i] != operatorBindingKey(binding, declarations) ||
        binding.symbol != witness.symbol)
      return refuse();
    bool chosen = sameTarget(binding.target, witness.target) &&
                  sameSpan(binding.span, *witness.origin);
    if (chosen) {
      for (unsigned j = 0; j < binding.arguments.size(); ++j)
        if (binding.arguments[j] &&
            *binding.arguments[j] != witness.arguments[j])
          return refuse();
      found = true;
      continue;
    }
    GroundMatch match(types, declarations[binding.target.declaration.index],
                      span);
    if (match.accepts(binding, inputs))
      return refuse();
    if (types.diagnostic)
      return false;
  }
  if (!found)
    return refuse();
  for (unsigned i = 0; i < inputs.size(); ++i) {
    auto type = types.substitute(selected.inputs[i].type, subst, span);
    if (!type || *type != inputs[i])
      return refuse();
  }
  auto result = types.substitute(selected.outputs.front().type, subst, span);
  return result && (*result == output || refuse());
}

bool checkCallAction(Semantics &types, ArrayRef<Declaration> declarations,
                     const Body &body, const Operation &operation) {
  auto refuse = [&] {
    return types.fail("source.binding-witness",
                      "resolved call differs from its native action",
                      operation.span);
  };
  if (!operation.binding ||
      operation.binding->target.declaration.index >= declarations.size())
    return refuse();
  const auto &binding = *operation.binding;
  const auto &callee = declarations[binding.target.declaration.index];
  if (binding.notation) {
    if (!binding.origin || binding.family.empty() ||
        binding.symbol != binding.notation->symbol)
      return refuse();
    // The selected declaration supplies an independent input count. A changed
    // descriptor and operand vector cannot certify one another.
    if (!checkNotationArity(types, *binding.notation, callee.inputs.size(),
                            operation.span))
      return false;
  } else if (!binding.symbol.empty() || !binding.family.empty() ||
             binding.origin) {
    return refuse();
  }
  if (binding.arguments.size() != callee.parameters.size() ||
      binding.operands.size() != callee.inputs.size() ||
      callee.outputs.size() != 1 || operation.results.size() != 1 ||
      operation.results.front().index >= body.values.size())
    return refuse();
  auto subst = types.substitution(callee, binding.arguments);
  if (binding.target.component && callee.parent)
    subst.emplace("self:" + declarations[callee.parent->index].qualifiedName,
                  *binding.target.component);
  for (unsigned i = 0; i < binding.operands.size(); ++i) {
    auto expected =
        types.substitute(callee.inputs[i].type, subst, operation.span);
    if (!expected || binding.operands[i].index >= body.values.size() ||
        *expected != body.values[binding.operands[i].index].type)
      return refuse();
  }
  auto result =
      types.substitute(callee.outputs.front().type, subst, operation.span);
  if (!result || *result != body.values[operation.results.front().index].type)
    return refuse();
  const auto *primitive = callee.primitive ? &*callee.primitive : nullptr;
  const auto *math =
      primitive ? mathematicalIntrinsic(primitive->identity) : nullptr;
  bool helper = !primitive || (body.mode == Body::Mode::Protocol && !math) ||
                (body.mode == Body::Mode::Local && math && !math->scalar);
  if (helper) {
    auto *action = std::get_if<HelperCall>(&operation.action);
    return (action && action->callee.index == callee.id.index &&
            action->arguments == binding.arguments &&
            action->component == binding.target.component &&
            sameOperands(action->operands, binding.operands)) ||
           refuse();
  }
  std::vector<Type> roots;
  for (const auto &arg : primitive->arguments) {
    auto value = types.substitute(arg, subst, operation.span);
    if (!value)
      return false;
    roots.push_back(std::move(*value));
  }
  if (body.mode == Body::Mode::Local) {
    auto *action = std::get_if<LocalPrimitive>(&operation.action);
    return (action && action->contract == primitive->identity &&
            sameOperands(action->operands, binding.operands) &&
            action->parameters.empty() && action->staticArguments.empty() &&
            action->assetReferences.empty() &&
            action->bindingArguments ==
                (math ? std::nullopt : std::optional(roots))) ||
           refuse();
  }
  auto *action = std::get_if<MathValue>(&operation.action);
  return (action && math && action->identity == math->identity &&
          sameOperands(action->operands, binding.operands) &&
          action->parameters.empty() && action->literal.empty() &&
          action->staticArguments ==
              (math->scalar ? std::vector<Type>{} : roots)) ||
         refuse();
}
} // namespace zkc::language::detail
