#include "MathematicalSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include <map>

using namespace mlir;
namespace zkc::poly {
namespace {
// A view of the current SSA, not a serialized expression graph. The candidate
// owns every emitted operation and is discarded on any failure.
class Elimination {
  OpBuilder builder;
  Degrees degrees;
  Operation *observation = nullptr;
  uint64_t &remaining;
  OptimizationOutcome *outcome;
  unsigned depth = 0;
  bool failed = false;
  using PointKey = std::pair<void *, std::vector<void *>>;
  std::map<PointKey, Value> evaluations;
  llvm::DenseMap<Value, SmallVector<Value>> coefficients;
  llvm::DenseMap<std::pair<Value, uint64_t>, Value> elements;
  llvm::DenseMap<algebra::FieldLiteralAttr, Value> constants;

  void refuse(llvm::StringRef detail) {
    if (!failed)
      diagnostics::emit(observation->emitOpError(), "polynomial-lowering",
                        detail);
    failed = true;
  }
  bool charge(uint64_t work = 1) {
    if (failed)
      return false;
    if (work > remaining) {
      if (outcome)
        *outcome = OptimizationOutcome::exhausted(WorkOwner::Polynomial, work,
                                                  remaining);
      refuse("static expansion exceeds 100000 work units");
      return false;
    }
    remaining -= work;
    return true;
  }
  Value make(llvm::StringRef name, Type type, ValueRange inputs = {},
             ArrayRef<NamedAttribute> attributes = {}) {
    if (!charge())
      return {};
    if (llvm::any_of(inputs, [](Value value) { return !value; })) {
      refuse("missing operand while realizing polynomial observation");
      return {};
    }
    OperationState state(observation->getLoc(), name);
    state.addTypes(type);
    state.addOperands(inputs);
    state.addAttributes(attributes);
    return builder.create(state)->getResult(0);
  }
  Value literal(algebra::FieldLiteralAttr value) {
    if (!value)
      return {};
    if (auto found = constants.find(value); found != constants.end())
      return found->second;
    auto result =
        make(algebra::ConstantFieldOp::getOperationName(), value.getField(), {},
             {builder.getNamedAttr("value", value)});
    if (result)
      constants.try_emplace(value, result);
    return result;
  }
  Value literal(algebra::FieldType field, const llvm::APInt &value) {
    auto attribute = algebra::makeFieldLiteral(field, value);
    if (!attribute) {
      llvm::consumeError(attribute.takeError());
      refuse("lowering requires an exact canonical field value");
      return {};
    }
    return literal(*attribute);
  }
  Value literal(algebra::FieldType field, uint64_t value) {
    return literal(field, llvm::APInt(64, value));
  }
  Value binary(llvm::StringRef name, Value a, Value b) {
    return a && b ? make(name, a.getType(), ValueRange{a, b}) : Value{};
  }
  Value add(Value a, Value b) {
    return binary(algebra::FieldAddOp::getOperationName(), a, b);
  }
  Value mul(Value a, Value b) {
    return binary(algebra::FieldMultiplyOp::getOperationName(), a, b);
  }
  Value subtract(Value a, Value b) {
    return binary(algebra::SubtractFieldOp::getOperationName(), a, b);
  }
  algebra::FieldType scalar(Value polynomial) {
    return algebra::FieldType::get(
        builder.getContext(),
        cast<PolynomialType>(polynomial.getType()).getDomain());
  }
  Value at(Value array, uint64_t index) {
    if (auto packed = array.getDefiningOp<algebra::ArrayFromElementsOp>())
      return packed.getElements()[index];
    auto key = std::make_pair(array, index);
    if (auto found = elements.find(key); found != elements.end())
      return found->second;
    auto type = cast<algebra::FieldArrayType>(array.getType()).getElementType();
    auto result =
        make(algebra::ArrayAtOp::getOperationName(), type, ValueRange{array},
             {builder.getNamedAttr("index", builder.getI64IntegerAttr(index))});
    if (result)
      elements[key] = result;
    return result;
  }
  SmallVector<Value> unpack(Value array) {
    auto length = cast<algebra::FieldArrayType>(array.getType()).getLength();
    if (!charge(length))
      return {};
    SmallVector<Value> result;
    for (uint64_t i = 0; i < length; ++i) {
      auto value = at(array, i);
      if (!value)
        return {};
      result.push_back(value);
    }
    return result;
  }
  Value pack(Type type, ArrayRef<Value> values) {
    return make(algebra::ArrayFromElementsOp::getOperationName(), type, values);
  }
  // Tables use lexicographic Boolean order: the first axis is the high bit.
  SmallVector<Value> fixTable(Value table, ValueRange prefix) {
    auto values = unpack(table);
    for (auto coordinate : prefix) {
      auto half = values.size() / 2;
      for (size_t i = 0; i < half; ++i) {
        auto delta = subtract(values[i + half], values[i]);
        values[i] = add(values[i], mul(coordinate, delta));
        if (!values[i])
          return {};
      }
      values.resize(half);
    }
    return values;
  }
  Value horner(ArrayRef<Value> values, Value point) {
    if (values.empty())
      return {};
    auto result = values.back();
    for (auto value : llvm::reverse(values.drop_back()))
      result = add(mul(result, point), value);
    return result;
  }
  // Compile-time Lagrange weights. Runtime data remains SSA; no runtime inverse
  // or claim that evaluation on a finite domain determines an arbitrary
  // polynomial.
  SmallVector<Value> interpolate(ArrayRef<Value> values,
                                 ArrayRef<algebra::FieldLiteralAttr> points,
                                 algebra::FieldType field) {
    if (values.size() != points.size() || points.empty() ||
        points.size() > MaximumDomainLength) {
      refuse("interpolation domain exceeds the installed 1..64 point "
             "implementation");
      return {};
    }
    auto modulus = protocol::fieldModulus(field.getDomain());
    if (modulus.empty() ||
        !protocol::installedDomains().hasFact("PrimeField",
                                              {field.getDomain().str()}) ||
        !llvm::all_of(modulus, [](char c) { return c >= '0' && c <= '9'; })) {
      refuse("interpolation requires an installed prime field with a decimal "
             "modulus");
      return {};
    }
    unsigned width = 2 * llvm::APInt::getBitsNeeded(modulus, 10) + 2;
    llvm::APInt p(width, modulus, 10), zero(width, 0), one(width, 1);
    auto product = [&](const llvm::APInt &a, const llvm::APInt &b) {
      return (a * b).urem(p);
    };
    auto difference = [&](const llvm::APInt &a, const llvm::APInt &b) {
      return (a + p - b).urem(p);
    };
    auto inverse = [&](llvm::APInt value) {
      auto power = p - 2;
      auto result = one;
      while (!power.isZero()) {
        if (power[0])
          result = product(result, value);
        value = product(value, value);
        power.lshrInPlace(1);
      }
      return result;
    };
    SmallVector<llvm::APInt> xs;
    for (auto point : points) {
      if (!point || point.getField() != field) {
        refuse("interpolation point has a different field identity");
        return {};
      }
      xs.push_back(point.getValue().getValue().zextOrTrunc(width));
    }
    SmallVector<Value> result(points.size(), literal(field, uint64_t(0)));
    for (size_t i = 0; i < xs.size(); ++i) {
      SmallVector<llvm::APInt> basis{one};
      auto denominator = one;
      for (size_t j = 0; j < xs.size(); ++j) {
        if (i == j)
          continue;
        if (xs[i] == xs[j]) {
          refuse("interpolation points are not distinct");
          return {};
        }
        if (!charge(basis.size()))
          return {};
        denominator = product(denominator, difference(xs[i], xs[j]));
        SmallVector<llvm::APInt> next(basis.size() + 1, zero);
        for (size_t k = 0; k < basis.size(); ++k) {
          next[k] = difference(next[k], product(xs[j], basis[k]));
          next[k + 1] = (next[k + 1] + basis[k]).urem(p);
        }
        basis = std::move(next);
      }
      if (!charge(width))
        return {};
      auto scale = inverse(denominator);
      for (size_t k = 0; k < basis.size(); ++k) {
        auto weight = literal(field, product(basis[k], scale));
        result[k] = add(result[k], mul(weight, values[i]));
        if (!result[k])
          return {};
      }
    }
    return result;
  }
  SmallVector<Value> coefficientValues(Value polynomial) {
    if (auto found = coefficients.find(polynomial); found != coefficients.end())
      return found->second;
    if (!charge() || depth >= 128) {
      refuse("polynomial expression depth exceeds 128");
      return {};
    }
    ++depth;
    llvm::scope_exit cleanup([&] { --depth; });
    auto *op = polynomial.getDefiningOp();
    SmallVector<Value> result;
    if (auto source = dyn_cast_or_null<CoefficientPolynomialOp>(op))
      result = unpack(source.getCoefficients());
    else if (auto constant = dyn_cast_or_null<ConstantPolynomialOp>(op))
      result = {constant.getScalar()};
    else if (isa_and_nonnull<AddPolynomialOp, MultiplyPolynomialOp>(op)) {
      auto a = coefficientValues(op->getOperand(0));
      auto b = coefficientValues(op->getOperand(1));
      if (a.empty() || b.empty())
        return {};
      bool multiply = isa<MultiplyPolynomialOp>(op);
      auto length =
          multiply ? a.size() + b.size() - 1 : std::max(a.size(), b.size());
      if (!charge(length))
        return {};
      auto zero = literal(scalar(polynomial), uint64_t(0));
      result.assign(length, zero);
      if (multiply) {
        if (a.size() > remaining / b.size()) {
          if (outcome)
            *outcome = OptimizationOutcome::exhausted(WorkOwner::Polynomial, {},
                                                      remaining);
          refuse("convolution exceeds expansion budget");
          return {};
        }
        for (size_t i = 0; i < a.size(); ++i)
          for (size_t j = 0; j < b.size(); ++j)
            result[i + j] = add(result[i + j], mul(a[i], b[j]));
      } else
        for (size_t i = 0; i < length; ++i)
          result[i] =
              add(i < a.size() ? a[i] : zero, i < b.size() ? b[i] : zero);
    } else if (auto interpolation = dyn_cast_or_null<InterpolateDomainOp>(op)) {
      auto values = unpack(interpolation.getValues());
      SmallVector<algebra::FieldLiteralAttr> points;
      for (auto point : interpolation.getPoints())
        points.push_back(cast<algebra::FieldLiteralAttr>(point));
      result = interpolate(values, points, scalar(polynomial));
    } else {
      auto found = degrees.bounds.find(polynomial);
      if (found == degrees.bounds.end() || found->second.size() != 1 ||
          found->second[0] >= MaximumDomainLength) {
        refuse("coefficient observation requires a derived degree below 64 for "
               "this recipe");
        return {};
      }
      SmallVector<algebra::FieldLiteralAttr> points;
      SmallVector<Value> values;
      for (uint64_t i = 0; i <= found->second[0]; ++i) {
        auto attribute =
            algebra::makeFieldLiteral(scalar(polynomial), llvm::APInt(64, i));
        if (!attribute) {
          llvm::consumeError(attribute.takeError());
          refuse("generated interpolation point exceeds the field");
          return {};
        }
        points.push_back(*attribute);
        auto point = literal(*attribute);
        if (!point)
          return {};
        values.push_back(evaluate(polynomial, ValueRange{point}));
        if (!values.back())
          return {};
      }
      result = interpolate(values, points, scalar(polynomial));
    }
    if (failed || llvm::any_of(result, [](Value v) { return !v; }))
      return {};
    coefficients[polynomial] = result;
    return result;
  }
  Value evaluate(Value polynomial, ValueRange point) {
    PointKey key{polynomial.getAsOpaquePointer(), {}};
    for (auto value : point)
      key.second.push_back(value.getAsOpaquePointer());
    if (auto found = evaluations.find(key); found != evaluations.end())
      return found->second;
    if (!charge() || depth >= 128) {
      refuse("polynomial expression depth exceeds 128");
      return {};
    }
    ++depth;
    llvm::scope_exit cleanup([&] { --depth; });
    auto *op = polynomial.getDefiningOp();
    Value result;
    if (auto constant = dyn_cast_or_null<ConstantPolynomialOp>(op))
      result = constant.getScalar();
    else if (isa_and_nonnull<CoefficientPolynomialOp, InterpolateDomainOp>(op))
      result = horner(coefficientValues(polynomial), point[0]);
    else if (auto mle = dyn_cast_or_null<MultilinearPolynomialOp>(op)) {
      auto values = fixTable(mle.getTable(), point);
      if (!values.empty())
        result = values.front();
    } else if (isa_and_nonnull<AddPolynomialOp, MultiplyPolynomialOp>(op)) {
      auto a = evaluate(op->getOperand(0), point);
      auto b = evaluate(op->getOperand(1), point);
      result = isa<AddPolynomialOp>(op) ? add(a, b) : mul(a, b);
    } else if (auto fix = dyn_cast_or_null<FixPolynomialOp>(op)) {
      SmallVector<Value> full(fix.getPrefix());
      llvm::append_range(full, point);
      result = evaluate(fix.getInput(), full);
    } else if (auto sum = dyn_cast_or_null<SumPolynomialOp>(op)) {
      auto count = uint64_t(sum.getCountAttr().getInt());
      auto size = uint64_t(1) << count;
      if (!charge(size))
        return {};
      auto field = scalar(polynomial);
      auto zero = literal(field, uint64_t(0)),
           one = literal(field, uint64_t(1));
      result = zero;
      for (uint64_t assignment = 0; assignment < size; ++assignment) {
        SmallVector<Value> full(point);
        for (uint64_t axis = 0; axis < count; ++axis)
          full.push_back((assignment >> (count - axis - 1)) & 1 ? one : zero);
        result = add(result, evaluate(sum.getInput(), full));
        if (!result)
          return {};
      }
    } else {
      refuse("unknown polynomial producer after preparation");
      return {};
    }
    if (result)
      evaluations.emplace(std::move(key), result);
    return result;
  }

public:
  explicit Elimination(MLIRContext *context, uint64_t &budget,
                       OptimizationOutcome *outcome = nullptr)
      : builder(context), remaining(budget), outcome(outcome) {}
  LogicalResult run(Block &body) {
    for (auto &op : body)
      for (auto &region : op.getRegions())
        for (auto &nested : region)
          if (mlir::failed(Elimination(builder.getContext(), remaining, outcome)
                               .run(nested)))
            return failure();
    if (mlir::failed(deriveDegrees(body, degrees)))
      return failure();
    eraseUnusedPolynomials(body, degrees);
    for (auto &operation : llvm::make_early_inc_range(body)) {
      observation = &operation;
      builder.setInsertionPoint(observation);
      Value result;
      if (auto eval = dyn_cast<EvaluatePolynomialOp>(observation))
        result = evaluate(eval.getPolynomial(), eval.getPoint());
      else if (auto observed =
                   dyn_cast<PolynomialCoefficientsOp>(observation)) {
        auto values = coefficientValues(observed.getPolynomial());
        auto length =
            cast<algebra::FieldArrayType>(observed.getCoefficients().getType())
                .getLength();
        if (!charge(length) || values.empty())
          return failure();
        values.resize(length,
                      literal(scalar(observed.getPolynomial()), uint64_t(0)));
        result = pack(observed.getCoefficients().getType(), values);
      } else if (auto domain = dyn_cast<EvaluateDomainOp>(observation)) {
        SmallVector<Value> values;
        for (auto point : domain.getPoints()) {
          auto coordinate = literal(cast<algebra::FieldLiteralAttr>(point));
          values.push_back(coordinate ? evaluate(domain.getPolynomial(),
                                                 ValueRange{coordinate})
                                      : Value{});
        }
        result = pack(domain.getValues().getType(), values);
      } else if (auto fix = dyn_cast<FixTableOp>(observation)) {
        auto values = fixTable(fix.getTable(), fix.getPrefix());
        if (values.empty())
          return failure();
        result = pack(fix.getResult().getType(), values);
      } else
        continue;
      if (!result || failed)
        return failure();
      observation->getResult(0).replaceAllUsesWith(result);
      observation->erase();
    }
    for (auto &op : llvm::make_early_inc_range(llvm::reverse(body))) {
      if (op.getNumResults() == 1 &&
          isa<PolynomialType>(op.getResult(0).getType())) {
        observation = &op;
        if (!op.use_empty()) {
          refuse("formal polynomial escapes its observations");
          return failure();
        }
        op.erase();
      }
    }
    return success();
  }
};
struct EliminatePolynomialsPass
    : PassWrapper<EliminatePolynomialsPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(EliminatePolynomialsPass)
  llvm::StringRef getArgument() const final {
    return "zkc-eliminate-polynomials";
  }
  llvm::StringRef getDescription() const final {
    return "Realize polynomial observations as bounded concrete field and "
           "nominal array operations";
  }
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<algebra::AlgebraDialect>();
  }
  void runOnOperation() final {
    auto source = getOperation();
    if (mlir::failed(zkc::admitStage(source)) ||
        !llvm::hasSingleElement(*source.getBody()))
      return signalPassFailure();
    auto original =
        dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
    if (!original ||
        original.getProfile() != protocol_ir::Profile::Participant) {
      diagnostics::emit(source.emitError(), "polynomial-lowering-profile",
                        "expected participant mathematics");
      return signalPassFailure();
    }
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    uint64_t remaining = 100000;
    for (auto participant :
         unit.getBody().front().getOps<protocol_ir::ParticipantOp>())
      if (mlir::failed(
              eliminatePolynomials(participant.getBody().front(), remaining)))
        return signalPassFailure();
    if (mlir::failed(zkc::admitStage(*candidate)) ||
        mlir::failed(
            mathematical::verifyProjectionPreserved(source, *candidate)))
      return signalPassFailure();
    source->setAttrs(candidate->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
  }
};
} // namespace
LogicalResult eliminatePolynomials(Block &body, uint64_t &remaining,
                                   OptimizationOutcome *outcome) {
  return Elimination(body.getParentOp()->getContext(), remaining, outcome)
      .run(body);
}
} // namespace zkc::poly
std::unique_ptr<mlir::Pass> zkc::protocol::createEliminatePolynomialsPass() {
  return std::make_unique<poly::EliminatePolynomialsPass>();
}
