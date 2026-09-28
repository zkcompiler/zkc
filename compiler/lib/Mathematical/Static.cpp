#include "zkc/Mathematical/Static.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <limits>

using namespace llvm;
namespace zkc::mathematical {

Error AdmissionBudget::consume(size_t amount) {
  if (amount > remaining)
    return error("math-admission-limit");
  if (charge)
    if (auto failure = charge(amount))
      return failure;
  remaining -= amount;
  return Error::success();
}
Static Static::literal(uint64_t value) { return {Kind::Literal, value, {}}; }
Static Static::parameter(uint64_t index) {
  return {Kind::Parameter, index, {}};
}
Static Static::add(Static left, Static right) {
  return {Kind::Add, 0, {std::move(left), std::move(right)}};
}
Static Static::multiply(Static left, Static right) {
  return {Kind::Multiply, 0, {std::move(left), std::move(right)}};
}
Static Static::pow2(Static exponent) {
  return {Kind::Pow2, 0, {std::move(exponent)}};
}
NormalStatic NormalStatic::literal(uint64_t value) {
  NormalStatic result;
  if (value)
    result.terms[{}] = value;
  return result;
}
NormalStatic NormalStatic::parameter(uint64_t index) {
  NormalStatic result;
  result.terms[{"p" + std::to_string(index)}] = 1;
  return result;
}
Expected<uint64_t> NormalStatic::closed() const {
  if (terms.empty())
    return 0;
  if (terms.size() == 1 && terms.begin()->first.empty())
    return terms.begin()->second;
  return error("math-open-static");
}
Expected<std::string> NormalStatic::key(AdmissionBudget &budget) const {
  std::string result;
  for (const auto &term : terms) {
    if (auto failure = budget.consume(1 + term.first.size()))
      return failure;
    result += std::to_string(term.second) + "[";
    for (const auto &atom : term.first) {
      if (auto failure = budget.consume(atom.size()))
        return failure;
      result += std::to_string(atom.size()) + ':' + atom;
    }
    result += "]";
  }
  return result;
}

namespace {
Expected<uint64_t> checkedAdd(uint64_t left, uint64_t right) {
  if (right > std::numeric_limits<uint64_t>::max() - left)
    return error("math-static-overflow");
  return left + right;
}
Expected<uint64_t> checkedMultiply(uint64_t left, uint64_t right) {
  if (right && left > std::numeric_limits<uint64_t>::max() / right)
    return error("math-static-overflow");
  return left * right;
}
Error chargeMonomial(const NormalStatic::Monomial &monomial,
                     AdmissionBudget &budget) {
  if (auto failure = budget.consume(1 + monomial.size()))
    return failure;
  for (const auto &atom : monomial)
    if (auto failure = budget.consume(atom.size()))
      return failure;
  return Error::success();
}
Error insert(NormalStatic::Terms &terms, const NormalStatic::Monomial &monomial,
             uint64_t coefficient, AdmissionBudget &budget) {
  // Symbolic power atoms can contain long normalized exponents. Charge their
  // bytes before a key copy, rather than just counting the number of atoms.
  if (auto failure = chargeMonomial(monomial, budget))
    return failure;
  if (!coefficient)
    return Error::success();
  auto found = terms.find(monomial);
  if (found == terms.end())
    terms.emplace(monomial, coefficient);
  else {
    auto sum = checkedAdd(found->second, coefficient);
    if (!sum) {
      if (monomial.empty())
        return sum.takeError();
      consumeError(sum.takeError());
      return error("math-admission-limit");
    }
    found->second = *sum;
  }
  return Error::success();
}
} // namespace

Expected<NormalStatic> normalize(const Static &expression,
                                 ArrayRef<NormalStatic> parameters,
                                 AdmissionBudget &budget, unsigned depth) {
  if (auto failure = budget.consume())
    return failure;
  if (depth > 64)
    return error("math-static-depth");
  size_t arity = expression.kind == Static::Kind::Pow2 ? 1 : 2;
  if (expression.kind == Static::Kind::Literal ||
      expression.kind == Static::Kind::Parameter)
    arity = 0;
  if (expression.operands.size() != arity || (arity && expression.value != 0))
    return error("math-static-shape");
  if (expression.kind == Static::Kind::Literal)
    return NormalStatic::literal(expression.value);
  if (expression.kind == Static::Kind::Parameter) {
    if (expression.value >= parameters.size())
      return error("math-static-scope");
    const auto &parameter = parameters[expression.value];
    // Charge all copied monomials and atom bytes before copying substitution.
    auto key = parameter.key(budget);
    if (!key)
      return key.takeError();
    return parameter;
  }
  auto left = normalize(expression.operands[0], parameters, budget, depth + 1);
  if (!left)
    return left.takeError();
  if (expression.kind == Static::Kind::Pow2) {
    auto constant = left->closed();
    if (constant) {
      if (*constant >= 64)
        return error("math-static-overflow");
      return NormalStatic::literal(uint64_t(1) << *constant);
    }
    consumeError(constant.takeError());
    auto exponent = left->key(budget);
    if (!exponent)
      return exponent.takeError();
    NormalStatic result;
    result.terms[{"e" + *exponent}] = 1;
    return result;
  }
  auto right = normalize(expression.operands[1], parameters, budget, depth + 1);
  if (!right)
    return right.takeError();
  if (expression.kind == Static::Kind::Add) {
    for (const auto &term : right->terms)
      if (auto failure = insert(left->terms, term.first, term.second, budget))
        return failure;
    return left;
  }
  if (expression.kind != Static::Kind::Multiply)
    return error("math-static-kind");
  NormalStatic result;
  for (const auto &a : left->terms)
    for (const auto &b : right->terms) {
      if (auto failure = chargeMonomial(a.first, budget))
        return failure;
      if (auto failure = chargeMonomial(b.first, budget))
        return failure;
      auto coefficient = checkedMultiply(a.second, b.second);
      if (!coefficient) {
        if (a.first.empty() && b.first.empty())
          return coefficient.takeError();
        consumeError(coefficient.takeError());
        return error("math-admission-limit");
      }
      NormalStatic::Monomial monomial;
      std::merge(a.first.begin(), a.first.end(), b.first.begin(), b.first.end(),
                 std::back_inserter(monomial));
      if (auto failure = insert(result.terms, monomial, *coefficient, budget))
        return failure;
    }
  return result;
}
Expected<NormalStatic> normalize(const Static &expression, uint64_t arity,
                                 AdmissionBudget &budget) {
  if (auto failure = budget.consume(arity))
    return failure;
  std::vector<NormalStatic> parameters;
  for (uint64_t i = 0; i < arity; ++i)
    parameters.push_back(NormalStatic::parameter(i));
  return normalize(expression, parameters, budget);
}
Expected<uint64_t> evaluate(const Static &expression,
                            ArrayRef<uint64_t> arguments,
                            AdmissionBudget &budget) {
  if (auto failure = budget.consume(arguments.size()))
    return failure;
  std::vector<NormalStatic> parameters;
  for (auto argument : arguments)
    parameters.push_back(NormalStatic::literal(argument));
  auto result = normalize(expression, parameters, budget);
  if (!result)
    return result.takeError();
  return result->closed();
}
} // namespace zkc::mathematical
