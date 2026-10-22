#include "Admission.h"
#include "lib/Dialect/ModArith/IR/ModArithOps.h"
#include "lib/Dialect/ModArith/IR/ModArithTypes.h"
#include "lib/Dialect/Polynomial/IR/PolynomialOps.h"
#include "lib/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "llvm/ADT/DenseMap.h"
#include <algorithm>
#include <cstdint>
#include <map>
#include <optional>
#include <vector>

using namespace mlir;
namespace poly = mlir::heir::polynomial;
namespace modular = mlir::heir::mod_arith;
namespace zkc::heir {
namespace {
// Expressions are polynomials in the ordered input ring elements. These are
// sufficient ring identities; failure to normalize is never a proof of
// inequivalence. No assumption that quotient elements form a field is used.
using Monomial = std::vector<unsigned>;
using Expression = std::map<Monomial, uint64_t>;
enum class Form { Raw, Modular, Coefficient, Evaluation, Lifted };
struct ValueMeaning {
  Expression expression;
  Form form = Form::Raw;
  uint64_t root = 0;
};
struct Subject {
  func::FuncOp function;
  uint64_t modulus = 0;
  uint64_t degree = 0;
  std::vector<Expression> outputs;
};

LogicalResult refuse(Operation *op, StringRef detail) {
  return op->emitError() << "heir-profile: " << detail;
}
bool attributes(Operation *op, ArrayRef<StringRef> allowed) {
  return llvm::all_of(op->getAttrs(), [&](NamedAttribute attr) {
    return llvm::is_contained(allowed, attr.getName().getValue());
  });
}
uint64_t power(uint64_t a, uint64_t exponent, uint64_t q) {
  uint64_t result = 1;
  while (exponent) {
    if (exponent & 1)
      result = result * a % q;
    a = a * a % q;
    exponent >>= 1;
  }
  return result;
}
bool prime(uint64_t q) {
  if (q < 3 || !(q & 1))
    return false;
  for (uint64_t divisor = 3; divisor * divisor <= q; divisor += 2)
    if (q % divisor == 0)
      return false;
  return true;
}

class Reader {
public:
  explicit Reader(ModuleOp module) : module(module) {}
  FailureOr<Subject> read() {
    if (failed(verify(module)) || !module->getAttrs().empty() ||
        !llvm::hasSingleElement(module.getBody()->getOperations()))
      return bad(module, "expected one attribute-free arithmetic module");
    auto function = dyn_cast<func::FuncOp>(module.getBody()->front());
    if (!function || function.isExternal() ||
        !function.getBody().hasOneBlock() ||
        !attributes(function,
                    {"sym_name", "sym_visibility", "function_type"}) ||
        function.getNumArguments() > 1024 || function.getNumResults() > 1024)
      return bad(module,
                 "expected a defined, single-block arithmetic function");
    subject.function = function;
    for (auto [index, argument] : llvm::enumerate(function.getArguments())) {
      if (!rawTensor(argument.getType()))
        return bad(function,
                   "expected fixed one-dimensional i32 coefficient inputs");
      values[argument] = {{{Monomial{unsigned(index)}, 1}}, Form::Raw, 0};
    }
    for (Type type : function.getResultTypes())
      if (!rawTensor(type))
        return bad(function,
                   "expected coefficient tensor outputs with the input degree");
    for (Operation &op : function.getBody().front()) {
      if (!spend(1 + op.getNumOperands() + op.getNumResults()) ||
          op.getNumRegions() || op.getNumSuccessors())
        return bad(&op, "unsupported control or arithmetic inspection limit");
      if (auto returned = dyn_cast<func::ReturnOp>(op)) {
        if (!attributes(&op, {}))
          return bad(&op, "unsupported return attribute");
        for (auto operand : returned.getOperands()) {
          auto found = values.find(operand);
          if (found == values.end() || found->second.form != Form::Lifted)
            return bad(&op, "outputs must observe standard coefficient lifts");
          subject.outputs.push_back(found->second.expression);
        }
      } else if (failed(readOperation(&op))) {
        return failure();
      }
    }
    if (!subject.modulus || subject.outputs.empty())
      return bad(function, "missing ring or coefficient observation");
    return subject;
  }

private:
  ModuleOp module;
  Subject subject;
  llvm::DenseMap<Value, ValueMeaning> values;
  uint64_t remaining = 1000000;
  FailureOr<Subject> bad(Operation *op, StringRef reason) {
    (void)refuse(op, reason);
    return failure();
  }
  bool spend(uint64_t cost) {
    if (cost > remaining)
      return false;
    remaining -= cost;
    return true;
  }
  bool degree(uint64_t n) {
    if (n < 2 || n > 65536 || (n & (n - 1)) ||
        (subject.degree && subject.degree != n))
      return false;
    subject.degree = n;
    return true;
  }
  bool rawTensor(Type type) {
    auto tensor = dyn_cast<RankedTensorType>(type);
    return tensor && !tensor.getEncoding() && tensor.getRank() == 1 &&
           tensor.getElementType().isSignlessInteger(32) &&
           tensor.hasStaticShape() && degree(tensor.getDimSize(0));
  }
  bool modulus(Type type) {
    auto modularType = dyn_cast<modular::ModArithType>(type);
    if (!modularType ||
        !modularType.getModulus().getType().isSignlessInteger(32))
      return false;
    auto q = modularType.getModulus().getValue().getZExtValue();
    // Keep canonical values signed-positive, and sums representable in i32.
    if (q >= (uint64_t{1} << 31) || !subject.degree ||
        (q - 1) % (2 * subject.degree) ||
        (subject.modulus ? q != subject.modulus : !prime(q)))
      return false;
    subject.modulus = q;
    return true;
  }
  bool modularTensor(Type type) {
    auto tensor = dyn_cast<RankedTensorType>(type);
    return tensor && !tensor.getEncoding() && tensor.getRank() == 1 &&
           tensor.hasStaticShape() && degree(tensor.getDimSize(0)) &&
           modulus(tensor.getElementType());
  }
  bool polynomial(Type type, Form expected) {
    auto polynomial = dyn_cast<poly::PolynomialType>(type);
    if (!polynomial || polynomial.getForm() != (expected == Form::Evaluation
                                                    ? poly::Form::EVAL
                                                    : poly::Form::COEFF))
      return false;
    auto ring = polynomial.getRing();
    auto quotient = ring.getPolynomialModulus();
    if (!quotient || !modulus(ring.getCoefficientType()))
      return false;
    auto quotientValue = quotient.getPolynomial();
    auto terms = quotientValue.getTerms();
    return terms.size() == 2 && terms[0].getExponent().isZero() &&
           terms[0].getCoefficient().isOne() &&
           terms[1].getCoefficient().isOne() &&
           terms[1].getExponent() == subject.degree;
  }
  std::optional<uint64_t> root(Operation *op) {
    auto attr = op->getAttrOfType<poly::PrimitiveRootAttr>("root");
    if (!attr || attr.getDegree().getValue() != 2 * subject.degree)
      return std::nullopt;
    auto value = dyn_cast<modular::ModArithAttr>(attr.getValue());
    if (!value || !modulus(value.getType()) ||
        value.getValue().getValue().getActiveBits() > 31)
      return std::nullopt;
    auto r = value.getValue().getValue().getZExtValue();
    if (!r || r >= subject.modulus ||
        power(r, subject.degree, subject.modulus) != subject.modulus - 1)
      return std::nullopt;
    return r;
  }
  bool accumulate(Expression &result, Monomial term, uint64_t coefficient) {
    if (!spend(1 + term.size()) || term.size() > 64)
      return false;
    auto &previous = result[term];
    previous = (previous + coefficient) % subject.modulus;
    if (!previous)
      result.erase(term);
    return true;
  }
  LogicalResult readOperation(Operation *op) {
    if (op->getNumResults() != 1 || op->getNumOperands() > 2 ||
        !op->getNumOperands())
      return refuse(op, "operation has no admitted arithmetic meaning");
    for (Value value : op->getOperands())
      if (!values.contains(value))
        return refuse(op, "operand has no admitted interpretation");
    const auto &left = values.find(op->getOperand(0))->second;
    if (!spend(left.expression.size()))
      return refuse(op, "arithmetic inspection limit");
    ValueMeaning result = left;
    Type output = op->getResult(0).getType();
    if (isa<modular::EncapsulateOp>(op)) {
      if (left.form != Form::Raw || !modularTensor(output) ||
          !attributes(op, {}))
        return refuse(
            op, "encapsulation must consume canonical input coefficients");
      result.form = Form::Modular;
    } else if (isa<poly::FromTensorOp>(op)) {
      if (left.form != Form::Modular ||
          !polynomial(output, Form::Coefficient) || !attributes(op, {}))
        return refuse(op, "unsupported coefficient construction");
      result.form = Form::Coefficient;
    } else if (isa<poly::ToTensorOp>(op)) {
      if (left.form != Form::Coefficient || !modularTensor(output) ||
          !attributes(op, {}))
        return refuse(op, "tensor observation requires coefficient form");
      result.form = Form::Modular;
    } else if (auto lift = dyn_cast<modular::LiftOp>(op)) {
      if (left.form != Form::Modular || !rawTensor(output) ||
          lift.getLiftType() != modular::LiftType::STANDARD ||
          !attributes(op, {"lift_type"}))
        return refuse(op, "only standard coefficient lifts are admitted");
      result.form = Form::Lifted;
    } else if (isa<poly::NTTOp, poly::INTTOp>(op)) {
      bool inverse = isa<poly::INTTOp>(op);
      Form inputForm = inverse ? Form::Evaluation : Form::Coefficient;
      Form outputForm = inverse ? Form::Coefficient : Form::Evaluation;
      auto r = root(op);
      if (left.form != inputForm || !polynomial(output, outputForm) || !r ||
          !attributes(op, {"root"}) ||
          (inverse && left.root * *r % subject.modulus != 1))
        return refuse(op,
                      "transform root does not preserve the evaluation basis");
      result.form = outputForm;
      result.root = inverse ? 0 : *r;
    } else if (isa<poly::AddOp, poly::SubOp, poly::MulOp>(op)) {
      const auto &right = values.find(op->getOperand(1))->second;
      if ((left.form != Form::Coefficient && left.form != Form::Evaluation) ||
          left.form != right.form || left.root != right.root ||
          !polynomial(output, left.form) || !attributes(op, {}))
        return refuse(
            op,
            "ring operands must share coefficient or evaluation coordinates");
      result.expression.clear();
      if (isa<poly::MulOp>(op)) {
        for (const auto &[a, x] : left.expression)
          for (const auto &[b, y] : right.expression) {
            if (a.size() + b.size() > 64)
              return refuse(op, "arithmetic monomial limit");
            Monomial term;
            std::merge(a.begin(), a.end(), b.begin(), b.end(),
                       std::back_inserter(term));
            if (!accumulate(result.expression, std::move(term),
                            x * y % subject.modulus))
              return refuse(op, "arithmetic inspection limit");
          }
      } else {
        for (const auto &[term, coefficient] : left.expression)
          if (!accumulate(result.expression, term, coefficient))
            return refuse(op, "arithmetic inspection limit");
        for (const auto &[term, coefficient] : right.expression)
          if (!accumulate(result.expression, term,
                          isa<poly::SubOp>(op) ? subject.modulus - coefficient
                                               : coefficient))
            return refuse(op, "arithmetic inspection limit");
      }
    } else {
      return refuse(op, "operation has no admitted arithmetic meaning");
    }
    values[op->getResult(0)] = std::move(result);
    return success();
  }
};
} // namespace

LogicalResult compareArithmetic(ModuleOp source, ModuleOp candidate) {
  auto original = Reader(source).read();
  if (failed(original))
    return failure();
  auto proposed = Reader(candidate).read();
  if (failed(proposed))
    return failure();
  if (original->function->getAttrDictionary() !=
          proposed->function->getAttrDictionary() ||
      original->modulus != proposed->modulus ||
      original->degree != proposed->degree ||
      original->outputs != proposed->outputs)
    return candidate->emitError(
        "heir-correspondence: arithmetic subject changed");
  return success();
}
} // namespace zkc::heir
