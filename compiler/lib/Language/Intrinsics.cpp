#include "BodyCheck.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<Checker::CallSignature>
Checker::intrinsicSignature(const Declaration *scope, StringRef name,
                            ArrayRef<Type> arguments,
                            ArrayRef<std::string> parameters, Span span) {
  const auto *intrinsic = mathematicalIntrinsic(name);
  using K = Type::Kind;
  if (intrinsic &&
      intrinsic->domain == MathematicalIntrinsic::Domain::Boolean) {
    if (!arguments.empty() || !parameters.empty()) {
      fail("source.intrinsic",
           "Boolean intrinsic has no static roots or parameters", span);
      return {};
    }
    return CallSignature{{Type{}, Type{}}, {Type{}}};
  }
  if (!intrinsic || arguments.size() != intrinsic->naturals + 1 ||
      arguments.front().kind != K::Field ||
      !llvm::all_of(arguments.drop_front(),
                    [](const Type &t) { return t.kind == K::Natural; })) {
    fail("source.intrinsic", "unknown intrinsic or static argument signature",
         span);
    return {};
  }
  for (const auto &argument : arguments)
    if (!chargeType(argument, span))
      return {};
  const auto &field = arguments.front();
  if ((!intrinsic->domainPoints && !parameters.empty()) ||
      (intrinsic->domainPoints &&
       (parameters.empty() || parameters.size() > 64))) {
    fail("source.intrinsic", "intrinsic domain parameter count differs", span);
    return {};
  }
  std::set<std::string> points;
  for (const auto &point : parameters) {
    if (!charge(point.size() + 1, span))
      return {};
    auto e = symbolic(field)
                 ? protocol::checkGenericParameters("field.constant", {point})
                 : protocol::checkParameters("field.constant", {point},
                                             field.domain);
    if (e) {
      fail("source.intrinsic", toString(std::move(e)), span);
      return {};
    }
    if (!points.insert(point).second) {
      fail("source.intrinsic", "domain points must be distinct", span);
      return {};
    }
  }
  auto natural = [](Natural n) {
    Type result(K::Natural);
    result.symbolic = !n.isClosed();
    result.dimension = std::move(n);
    return result;
  };
  auto normalize = [&](Expected<Natural> n,
                       uint64_t before) -> std::optional<Type> {
    if (!n) {
      accept(n.takeError());
      return {};
    }
    if (!charge(before - naturals.remainingWork(), span))
      return {};
    return natural(std::move(*n));
  };
  auto add = [&](const Type &a, const Type &b) {
    auto before = naturals.remainingWork();
    return normalize(naturals.add(a.dimension, b.dimension), before);
  };
  auto pow2 = [&](const Type &a) {
    auto before = naturals.remainingWork();
    return normalize(naturals.powerOfTwo(a.dimension), before);
  };
  auto one = natural(Natural::constant(1));
  auto bound = [&](const Type &a, const Type &b) {
    if (scope)
      return assumptions(*scope, {a.dimension, b.dimension, span}, {}, span);
    return (a.dimension.isClosed() && b.dimension.isClosed() &&
            a.dimension.closedValue() <= b.dimension.closedValue()) ||
           fail("source.bound", "closed intrinsic natural requirement is false",
                span);
  };
  auto shape = [&](bool formal, const Type &n) -> std::optional<Type> {
    auto result = formal ? formalType("polynomial", {field, n})
                         : builtinType("field_array", {field, n});
    if (!result) {
      fail("source.intrinsic", toString(result.takeError()), span);
      return {};
    }
    return std::move(*result);
  };
  auto array = [&](const Type &n) -> std::optional<Type> {
    if (n.dimension.isClosed() &&
        n.dimension.closedValue() > work.limits.aggregateLeaves) {
      fail("source.limit", "intrinsic fixed array exceeds leaf limit", span);
      return {};
    }
    Type result(K::Array);
    result.arguments = {field};
    result.dimension = n.dimension;
    return result;
  };
  CallSignature result;
  auto input = [&](std::optional<Type> type) {
    if (!type)
      return false;
    result.inputs.push_back(std::move(*type));
    return true;
  };
  auto output = [&](std::optional<Type> type) {
    if (!type)
      return false;
    result.outputs.push_back(std::move(*type));
    return true;
  };
  using I = MathematicalIdentity;
  // Arity/length relationships are checked symbolically; native admission owns
  // closed representation and degree limits. No polynomial evaluator lives
  // here.
  auto n = intrinsic->naturals ? arguments[1]
                               : natural(Natural::constant(parameters.size()));
  switch (intrinsic->identity) {
  case I::ArrayFromElements:
    if (!input(array(n)) || !output(shape(false, n)))
      return {};
    break;
  case I::ArrayAt: {
    auto end = add(arguments[2], one);
    if (!end || !bound(*end, n) || !input(shape(false, n)) || !output(field))
      return {};
    break;
  }
  case I::PolynomialConstant:
    if (!input(field) || !output(shape(true, n)))
      return {};
    break;
  case I::PolynomialFromCoefficients:
    if (!bound(one, n) || !input(shape(false, n)) || !output(shape(true, one)))
      return {};
    break;
  case I::PolynomialMLE: {
    auto length = pow2(n);
    if (!length || !input(shape(false, *length)) || !output(shape(true, n)))
      return {};
    break;
  }
  case I::PolynomialAdd:
  case I::PolynomialMultiply:
    if (!input(shape(true, n)) || !input(shape(true, n)) ||
        !output(shape(true, n)))
      return {};
    break;
  case I::PolynomialFix:
  case I::PolynomialSum: {
    auto arity = add(n, arguments[2]);
    if (!arity || !input(shape(true, *arity)))
      return {};
    if (intrinsic->identity == I::PolynomialFix && !input(array(arguments[2])))
      return {};
    if (!output(shape(true, n)))
      return {};
    break;
  }
  case I::PolynomialEvaluate:
    if (!input(shape(true, n)) || !input(array(n)) || !output(field))
      return {};
    break;
  case I::PolynomialCoefficients:
    if (!bound(one, n) || !input(shape(true, one)) || !output(shape(false, n)))
      return {};
    break;
  case I::PolynomialEvaluateDomain:
    if (!input(shape(true, one)) || !output(shape(false, n)))
      return {};
    break;
  case I::PolynomialInterpolate:
    if (!input(shape(false, n)) || !output(shape(true, one)))
      return {};
    break;
  case I::PolynomialFixTable: {
    auto arity = add(n, arguments[2]);
    if (!arity)
      return {};
    auto length = pow2(*arity), residual = pow2(n);
    if (!length || !residual || !input(shape(false, *length)) ||
        !input(array(arguments[2])) || !output(shape(false, *residual)))
      return {};
    break;
  }
  default:
    fail("source.intrinsic", "mathematical identity has no authoring signature",
         span);
    return {};
  }
  return result;
}
std::optional<Checker::CallSignature>
BodyChecker::intrinsicSignature(const Expression &expr,
                                std::vector<Type> &arguments) {
  for (const auto &syntax : expr.arguments) {
    auto type = checker.type(decl, syntax);
    if (!type)
      return {};
    arguments.push_back(std::move(*type));
  }
  return checker.intrinsicSignature(&decl, expr.text, arguments, expr.labels,
                                    expr.span);
}
std::optional<ValueId> BodyChecker::intrinsic(const Expression &expr,
                                              unsigned depth) {
  if (!math()) {
    fail("source.mode", "mathematical intrinsics require a math function",
         expr.span);
    return {};
  }
  std::vector<Type> arguments;
  auto signature = intrinsicSignature(expr, arguments);
  if (!signature)
    return {};
  if (expr.children.size() != signature->inputs.size()) {
    fail("source.intrinsic", "intrinsic input count differs", expr.span);
    return {};
  }
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto value = expression(expr.children[i], signature->inputs[i], depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    operands.push_back(*value);
  }
  auto components = combine(operands, expr.span);
  if (!components)
    return {};
  return emit(MathValue{mathematicalIntrinsic(expr.text)->identity,
                        std::move(operands),
                        {},
                        std::move(arguments),
                        expr.labels},
              signature->resultType(), std::move(*components), expr.span);
}
} // namespace zkc::language::detail
