#include "NormalizationVerification.h"
#include "../HelperNormalization.h"
#include "../MathematicalValues.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Interfaces/Collection.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>
#include <iterator>
#include <limits>
#include <map>
#include <string>
#include <vector>

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
bool polynomial(Operation &op) {
  return poly::isPolynomialNormalizationOperation(&op);
}
bool flatTotal(Operation &op) {
  return !op.getNumRegions() && !op.getNumSuccessors() &&
         mathematical::isTotal(&op);
}
bool sameShape(Operation &source, Operation &candidate) {
  return flatTotal(source) && flatTotal(candidate) &&
         source.getName() == candidate.getName() &&
         source.getAttrDictionary() == candidate.getAttrDictionary() &&
         source.getNumOperands() == candidate.getNumOperands() &&
         source.getResultTypes() == candidate.getResultTypes();
}
} // namespace

struct NormalizationProvenanceChecker::Implementation {
  Operation *root;
  // Structural reads and independent interpolation laws share this budget.
  mathematical::ValueCorrespondence terms;
  mathematical::HelperNormalizationChecker meaning;
  SymbolTableCollection symbols;
  bool depthExhausted = false;

  Implementation(Operation *root, size_t work)
      : root(root), terms(root, false, work), meaning(root, work) {}

  bool charge(Operation &op) {
    return terms.charge(1 + size_t(op.getNumOperands()) + op.getNumResults());
  }
  LogicalResult refuse(Operation *subject, StringRef detail) {
    return diagnostics::emit(subject->emitOpError(),
                             terms.workExhausted() || depthExhausted
                                 ? "kernel-normalization-limit"
                                 : "kernel-normalization-provenance",
                             detail);
  }
  bool interface(func::FuncOp source, Block &candidate) {
    return source && source.getBody().hasOneBlock() &&
           !source.front().empty() && !candidate.empty() &&
           llvm::equal(source.getArgumentTypes(),
                       candidate.getArgumentTypes()) &&
           isa<func::ReturnOp>(source.front().back()) &&
           isa<func::ReturnOp>(candidate.back()) &&
           source.front().back().getAttrDictionary() ==
               candidate.back().getAttrDictionary() &&
           llvm::equal(source.getResultTypes(),
                       source.front().back().getOperandTypes()) &&
           llvm::equal(source.getResultTypes(),
                       candidate.back().getOperandTypes());
  }

  // Consume the actual expansion directly, using an invocation-local exact SSA
  // map. No memoization of invocations: repeated calls each contribute work,
  // including operations whose results never escape the call.
  struct Expansion {
    Implementation &check;
    Block::iterator cursor;
    Block::iterator end;
    llvm::DenseSet<Operation *> active;

    FailureOr<SmallVector<Value>> read(func::FuncOp source,
                                       ValueRange arguments) {
      if (active.size() >= 64) {
        check.depthExhausted = true;
        return failure();
      }
      if (!source || !source.getBody().hasOneBlock() ||
          source.front().empty() ||
          source.getNumArguments() != arguments.size() ||
          !active.insert(source).second || !check.charge(*source))
        return failure();
      auto leave = llvm::scope_exit([&] { active.erase(source); });
      llvm::DenseMap<Value, Value> values;
      for (auto [formal, actual] : zip(source.getArguments(), arguments)) {
        if (!actual || formal.getType() != actual.getType() ||
            !check.terms.charge())
          return failure();
        values[formal] = actual;
      }
      for (auto &op : source.front().without_terminator()) {
        if (!check.charge(op) || op.getNumRegions() || op.getNumSuccessors())
          return failure();
        SmallVector<Value> inputs, outputs;
        for (Value operand : op.getOperands()) {
          auto actual = values.lookup(operand);
          if (!actual)
            return failure();
          inputs.push_back(actual);
        }
        if (auto call = dyn_cast<func::CallOp>(op)) {
          // Admission owns the function-level contracts. A call with extra
          // attributes cannot be silently erased by this substitution edge.
          for (auto attr : call->getAttrs())
            if (attr.getName().getValue() != "callee")
              return failure();
          auto helper = check.symbols.lookupSymbolIn<func::FuncOp>(
              check.root, call.getCalleeAttr());
          auto returned = read(helper, inputs);
          if (failed(returned) || returned->size() != op.getNumResults())
            return failure();
          outputs = std::move(*returned);
        } else {
          if (cursor == end || !check.charge(*cursor) ||
              !sameShape(op, *cursor) ||
              !llvm::equal(inputs, cursor->getOperands()))
            return failure();
          append_range(outputs, cursor->getResults());
          ++cursor;
        }
        for (auto [before, after] : zip(op.getResults(), outputs)) {
          if (before.getType() != after.getType())
            return failure();
          values[before] = after;
        }
      }
      auto &ret = source.front().back();
      if (!isa<func::ReturnOp>(ret) || !ret.getAttrs().empty() ||
          !check.charge(ret) ||
          !llvm::equal(source.getResultTypes(), ret.getOperandTypes()))
        return failure();
      SmallVector<Value> outputs;
      for (Value value : ret.getOperands()) {
        auto actual = values.lookup(value);
        if (!actual)
          return failure();
        outputs.push_back(actual);
      }
      return outputs;
    }
  };

  // This is an instruction reader, not a proposed replacement body. Concrete
  // values are actual SSA handles throughout; polynomial descriptions refer to
  // source SSA. Only defining polynomial laws may consume extra instructions.
  struct Normalization {
    Implementation &check;
    func::FuncOp source;
    Block &candidate;
    Block::iterator cursor;
    Builder attributes;
    llvm::DenseMap<Value, Value> values;
    llvm::DenseSet<Operation *> live;
    llvm::DenseMap<Value, SmallVector<uint64_t>> degrees;
    llvm::DenseMap<Value, SmallVector<Value>> coefficients;
    using EvaluationKey = std::pair<void *, std::vector<void *>>;
    std::map<EvaluationKey, Value> evaluations;
    llvm::DenseMap<std::pair<Value, uint64_t>, Value> elements;
    std::map<std::pair<const void *, std::string>, Value> constants;
    SmallVector<Operation *> generated;
    unsigned depth = 0;
    bool invalid = false;

    Normalization(Implementation &check, func::FuncOp source, Block &candidate)
        : check(check), source(source), candidate(candidate),
          cursor(candidate.begin()), attributes(source.getContext()) {}

    bool enter() {
      if (depth >= 128) {
        check.depthExhausted = true;
        return false;
      }
      ++depth;
      return check.terms.charge();
    }
    Value make(StringRef name, Type type, ValueRange inputs = {},
               ArrayRef<NamedAttribute> attrs = {}) {
      if (invalid || cursor == candidate.end() ||
          !check.terms.charge(1 + inputs.size()) ||
          llvm::any_of(inputs, [](Value value) { return !value; })) {
        invalid = true;
        return {};
      }
      Operation &actual = *cursor;
      if (!check.charge(actual) || !flatTotal(actual) || polynomial(actual) ||
          actual.getName().getStringRef() != name ||
          actual.getNumResults() != 1 ||
          actual.getResult(0).getType() != type ||
          !llvm::equal(actual.getOperands(), inputs) ||
          actual.getAttrDictionary() != attributes.getDictionaryAttr(attrs)) {
        invalid = true;
        return {};
      }
      generated.push_back(&actual);
      ++cursor;
      return actual.getResult(0);
    }
    Value literal(algebra::FieldType type, StringRef value) {
      if (!check.terms.charge())
        return {};
      auto key = std::make_pair(type.getAsOpaquePointer(), value.str());
      if (auto found = constants.find(key); found != constants.end())
        return found->second;
      if (!algebra::isCanonicalFieldLiteral(type.getDomain(), value))
        return {};
      auto result = make(
          "algebra.constant", type, {},
          {attributes.getNamedAttr("value", attributes.getStringAttr(value))});
      if (result)
        constants.emplace(std::move(key), result);
      return result;
    }
    Value binary(StringRef name, Value a, Value b) {
      return a && b ? make(name, a.getType(), ValueRange{a, b}) : Value{};
    }
    Value add(Value a, Value b) { return binary("algebra.field_add", a, b); }
    Value multiply(Value a, Value b) {
      return binary("algebra.field_multiply", a, b);
    }
    Value subtract(Value a, Value b) {
      return binary("algebra.field_subtract", a, b);
    }
    algebra::FieldType scalar(Value polynomial) {
      return algebra::FieldType::get(
          source.getContext(),
          cast<poly::PolynomialType>(polynomial.getType()).getDomain());
    }
    Value at(Value array, uint64_t index) {
      if (!array || !check.terms.charge())
        return {};
      auto type = dyn_cast<algebra::FieldArrayType>(array.getType());
      if (!type || index >= uint64_t(type.getLength()))
        return {};
      // Definitional pack observation within a polynomial law. The concrete
      // pack itself was already consumed and is never deleted or conflated.
      if (auto pack = array.getDefiningOp<algebra::ArrayFromElementsOp>())
        return pack.getElements()[index];
      auto key = std::make_pair(array, index);
      if (auto found = elements.find(key); found != elements.end())
        return found->second;
      auto result = make("algebra.array_at", type.getElementType(), {array},
                         {attributes.getNamedAttr(
                             "index", attributes.getI64IntegerAttr(index))});
      if (result)
        elements[key] = result;
      return result;
    }
    SmallVector<Value> unpack(Value array) {
      if (!array)
        return {};
      auto type = dyn_cast<algebra::FieldArrayType>(array.getType());
      if (!type || !check.terms.charge(type.getLength()))
        return {};
      SmallVector<Value> result;
      for (uint64_t i = 0; i < uint64_t(type.getLength()); ++i) {
        auto value = at(array, i);
        if (!value)
          return {};
        result.push_back(value);
      }
      return result;
    }
    Value pack(Type type, ArrayRef<Value> inputs) {
      return make("algebra.array_from_elements", type, inputs);
    }
    SmallVector<Value> fixTable(Value table, ValueRange prefix) {
      auto result = unpack(table);
      for (Value point : prefix) {
        if (result.empty() || result.size() % 2 ||
            !check.terms.charge(result.size()))
          return {};
        unsigned half = result.size() / 2;
        for (unsigned i = 0; i < half; ++i) {
          auto delta = subtract(result[i + half], result[i]);
          result[i] = add(result[i], multiply(point, delta));
          if (!result[i])
            return {};
        }
        result.resize(half);
      }
      return result;
    }
    Value horner(ArrayRef<Value> coefficients, Value point) {
      if (coefficients.empty())
        return {};
      Value result = coefficients.back();
      for (Value coefficient : llvm::reverse(coefficients.drop_back()))
        result = add(multiply(result, point), coefficient);
      return result;
    }

    // Obtain weights from the existing independent Vandermonde laws. Unique
    // sample anchors prevent equal-valued samples from identifying coordinates.
    // Only numeric weights are extracted; no expected MLIR is ever generated.
    FailureOr<SmallVector<SmallVector<std::string>>>
    weights(algebra::FieldType field, ArrayAttr points) {
      using Term = mathematical::ValueCorrespondence::Term;
      unsigned n = points.size();
      if (!n || n > 64 || !check.terms.charge(n * n))
        return failure();
      auto &terms = check.terms;
      SmallVector<Term> samples;
      for (unsigned i = 0; i < n; ++i)
        samples.push_back(terms.anchor(field));
      auto array = algebra::FieldArrayType::get(source.getContext(),
                                                field.getDomain(), n);
      auto empty = attributes.getDictionaryAttr({});
      Term table = terms.expression("algebra.array_from_elements", array, empty,
                                    samples);
      Term polynomial = terms.expression(
          "poly.interpolate",
          poly::PolynomialType::get(source.getContext(), field.getDomain(), 1),
          attributes.getDictionaryAttr(
              {attributes.getNamedAttr("points", points)}),
          {table});
      Term observation =
          terms.expression("poly.coefficients", array, empty, {polynomial});
      if (!table || !polynomial || !observation)
        return failure();
      mathematical::PolynomialValueCache cache;
      Term normal =
          mathematical::normalizePolynomialValues(terms, observation, cache);
      if (!normal)
        return failure();
      auto packed = terms.expression(normal);
      if (!packed.name ||
          packed.name.getValue() != "algebra.array_from_elements" ||
          packed.operands.size() != n)
        return failure();
      SmallVector<SmallVector<std::string>> result(n);
      for (unsigned degree = 0; degree < n; ++degree) {
        result[degree].resize(n);
        Term partial = packed.operands[degree];
        for (unsigned sample = n; sample-- > 0;) {
          if (!terms.charge())
            return failure();
          auto sum = terms.expression(partial);
          if (!sum.name || sum.name.getValue() != "algebra.field_add" ||
              sum.operands.size() != 2)
            return failure();
          auto product = terms.expression(sum.operands[1]);
          if (!product.name ||
              product.name.getValue() != "algebra.field_multiply" ||
              product.operands.size() != 2 ||
              product.operands[1] != samples[sample])
            return failure();
          auto weight = terms.expression(product.operands[0]);
          auto spelling = weight.attributes
                              ? weight.attributes.getAs<StringAttr>("value")
                              : StringAttr{};
          if (!weight.name || weight.name.getValue() != "algebra.constant" ||
              weight.type != field || !spelling)
            return failure();
          result[degree][sample] = spelling.getValue().str();
          partial = sum.operands[0];
        }
      }
      return result;
    }
    SmallVector<Value> interpolate(ArrayRef<Value> samples, ArrayAttr points,
                                   algebra::FieldType field) {
      if (samples.size() != points.size())
        return {};
      auto matrix = weights(field, points);
      if (failed(matrix))
        return {};
      SmallVector<Value> result(samples.size(), literal(field, "0"));
      // Consume the supported scalar realization in sample-major order. The
      // weights above were derived independently in coefficient-major order.
      for (unsigned sample = 0; sample < samples.size(); ++sample)
        for (unsigned degree = 0; degree < samples.size(); ++degree) {
          auto weight = literal(field, (*matrix)[degree][sample]);
          result[degree] =
              add(result[degree], multiply(weight, samples[sample]));
          if (!result[degree])
            return {};
        }
      return result;
    }

    SmallVector<Value> coefficientValues(Value polynomial) {
      if (auto found = coefficients.find(polynomial);
          found != coefficients.end())
        return found->second;
      if (!enter())
        return {};
      auto leave = llvm::scope_exit([&] { --depth; });
      auto *op = polynomial.getDefiningOp();
      SmallVector<Value> result;
      if (auto from = dyn_cast_or_null<poly::CoefficientPolynomialOp>(op))
        result = unpack(values.lookup(from.getCoefficients()));
      else if (auto constant = dyn_cast_or_null<poly::ConstantPolynomialOp>(op))
        result = {values.lookup(constant.getScalar())};
      else if (isa_and_nonnull<poly::AddPolynomialOp,
                               poly::MultiplyPolynomialOp>(op)) {
        auto a = coefficientValues(op->getOperand(0));
        auto b = coefficientValues(op->getOperand(1));
        if (a.empty() || b.empty())
          return {};
        bool product = isa<poly::MultiplyPolynomialOp>(op);
        size_t width =
            product ? a.size() + b.size() - 1 : std::max(a.size(), b.size());
        if (!check.terms.charge(width) ||
            (product && !check.terms.charge(a.size() * b.size())))
          return {};
        auto zero = literal(scalar(polynomial), "0");
        if (!zero)
          return {};
        result.assign(width, zero);
        if (product) {
          for (unsigned i = 0; i < a.size(); ++i)
            for (unsigned j = 0; j < b.size(); ++j)
              result[i + j] = add(result[i + j], multiply(a[i], b[j]));
        } else {
          for (unsigned i = 0; i < width; ++i)
            result[i] =
                add(i < a.size() ? a[i] : zero, i < b.size() ? b[i] : zero);
        }
      } else if (auto interpolation =
                     dyn_cast_or_null<poly::InterpolateDomainOp>(op)) {
        auto samples = unpack(values.lookup(interpolation.getValues()));
        if (samples.empty())
          return {};
        result =
            interpolate(samples, interpolation.getPoints(), scalar(polynomial));
      } else {
        auto bound = degrees.find(polynomial);
        if (bound == degrees.end() || bound->second.size() != 1 ||
            bound->second[0] >= 64)
          return {};
        SmallVector<Attribute> points;
        SmallVector<Value> samples;
        for (uint64_t i = 0; i <= bound->second[0]; ++i) {
          auto spelling = std::to_string(i);
          points.push_back(attributes.getStringAttr(spelling));
          auto point = literal(scalar(polynomial), spelling);
          if (!point)
            return {};
          auto sample = evaluate(polynomial, {point});
          if (!sample)
            return {};
          samples.push_back(sample);
        }
        result = interpolate(samples, attributes.getArrayAttr(points),
                             scalar(polynomial));
      }
      if (result.empty() || is_contained(result, Value{}))
        return {};
      coefficients[polynomial] = result;
      return result;
    }
    Value evaluate(Value polynomial, ValueRange point) {
      EvaluationKey key{polynomial.getAsOpaquePointer(), {}};
      for (auto value : point)
        key.second.push_back(value.getAsOpaquePointer());
      if (auto found = evaluations.find(key); found != evaluations.end())
        return found->second;
      if (!enter())
        return {};
      auto leave = llvm::scope_exit([&] { --depth; });
      auto *op = polynomial.getDefiningOp();
      Value result;
      if (auto constant = dyn_cast_or_null<poly::ConstantPolynomialOp>(op))
        result = values.lookup(constant.getScalar());
      else if (isa_and_nonnull<poly::CoefficientPolynomialOp,
                               poly::InterpolateDomainOp>(op)) {
        if (point.size() != 1)
          return {};
        result = horner(coefficientValues(polynomial), point[0]);
      } else if (auto mle =
                     dyn_cast_or_null<poly::MultilinearPolynomialOp>(op)) {
        auto table = fixTable(values.lookup(mle.getTable()), point);
        if (table.size() == 1)
          result = table.front();
      } else if (isa_and_nonnull<poly::AddPolynomialOp,
                                 poly::MultiplyPolynomialOp>(op)) {
        auto a = evaluate(op->getOperand(0), point);
        auto b = evaluate(op->getOperand(1), point);
        result = isa<poly::AddPolynomialOp>(op) ? add(a, b) : multiply(a, b);
      } else if (auto fix = dyn_cast_or_null<poly::FixPolynomialOp>(op)) {
        SmallVector<Value> full;
        for (auto prefix : fix.getPrefix()) {
          auto actual = values.lookup(prefix);
          if (!actual)
            return {};
          full.push_back(actual);
        }
        append_range(full, point);
        result = evaluate(fix.getInput(), full);
      } else if (auto sum = dyn_cast_or_null<poly::SumPolynomialOp>(op)) {
        auto count = sum.getCountAttr().getInt();
        if (count < 0 || count >= 63 ||
            !check.terms.charge(uint64_t(1) << count))
          return {};
        auto field = scalar(polynomial);
        auto zero = literal(field, "0");
        auto one = literal(field, "1");
        if (!zero || !one)
          return {};
        result = zero;
        for (uint64_t assignment = 0; assignment < (uint64_t(1) << count);
             ++assignment) {
          SmallVector<Value> full(point);
          for (int64_t axis = count; axis-- > 0;)
            full.push_back((assignment >> axis) & 1 ? one : zero);
          result = add(result, evaluate(sum.getInput(), full));
          if (!result)
            return {};
        }
      }
      if (result)
        evaluations.emplace(std::move(key), result);
      return result;
    }

    bool degree(Operation &op) {
      if (op.getNumResults() != 1)
        return false;
      auto type = dyn_cast<poly::PolynomialType>(op.getResult(0).getType());
      if (!type)
        return isa<poly::EvaluatePolynomialOp, poly::PolynomialCoefficientsOp,
                   poly::EvaluateDomainOp, poly::FixTableOp>(op);
      if (!check.terms.charge(1 + type.getArity()))
        return false;
      SmallVector<uint64_t> bound;
      if (isa<poly::ConstantPolynomialOp>(op))
        bound.assign(type.getArity(), 0);
      else if (isa<poly::MultilinearPolynomialOp>(op))
        bound.assign(type.getArity(), 1);
      else if (isa<poly::CoefficientPolynomialOp, poly::InterpolateDomainOp>(
                   op)) {
        auto array =
            dyn_cast<algebra::FieldArrayType>(op.getOperand(0).getType());
        if (!array || array.getLength() <= 0)
          return false;
        bound.push_back(array.getLength() - 1);
      } else {
        auto first = degrees.find(op.getOperand(0));
        if (first == degrees.end())
          return false;
        bound = first->second;
        if (isa<poly::AddPolynomialOp, poly::MultiplyPolynomialOp>(op)) {
          auto second = degrees.find(op.getOperand(1));
          if (second == degrees.end() || bound.size() != second->second.size())
            return false;
          for (auto [a, b] : zip(bound, second->second)) {
            if (isa<poly::AddPolynomialOp>(op))
              a = std::max(a, b);
            else {
              if (a > std::numeric_limits<uint64_t>::max() - b)
                return false;
              a += b;
            }
          }
        } else if (auto fix = dyn_cast<poly::FixPolynomialOp>(op)) {
          if (fix.getPrefix().size() > bound.size())
            return false;
          bound.erase(bound.begin(), bound.begin() + fix.getPrefix().size());
        } else if (auto sum = dyn_cast<poly::SumPolynomialOp>(op)) {
          if (sum.getCountAttr().getInt() < 0 ||
              uint64_t(sum.getCountAttr().getInt()) > bound.size())
            return false;
          bound.resize(bound.size() - sum.getCountAttr().getInt());
        } else
          return false;
      }
      if (bound.size() != type.getArity())
        return false;
      degrees[op.getResult(0)] = std::move(bound);
      return true;
    }
    bool run() {
      for (auto [before, after] :
           zip(source.getArguments(), candidate.getArguments())) {
        if (!check.terms.charge())
          return false;
        values[before] = after;
      }
      // Independently compute which polynomial descriptions/observations can
      // disappear. Every concrete operation is a root, even if itself unused.
      llvm::DenseSet<Value> needed;
      for (Value returned : source.front().back().getOperands()) {
        if (!check.terms.charge())
          return false;
        needed.insert(returned);
      }
      for (auto &op : llvm::reverse(source.front().without_terminator())) {
        if (!check.charge(op))
          return false;
        if (polynomial(op) && llvm::none_of(op.getResults(), [&](Value value) {
              return needed.contains(value);
            }))
          continue;
        live.insert(&op);
        for (auto operand : op.getOperands())
          needed.insert(operand);
      }
      for (auto &op : source.front().without_terminator()) {
        if (!check.charge(op) || !flatTotal(op) || isa<func::CallOp>(op))
          return false;
        if (!polynomial(op)) {
          if (cursor == candidate.end() || !check.charge(*cursor) ||
              !sameShape(op, *cursor))
            return false;
          for (auto [before, after] :
               zip(op.getOperands(), cursor->getOperands()))
            if (!values.lookup(before) || values.lookup(before) != after)
              return false;
          for (auto [before, after] :
               zip(op.getResults(), cursor->getResults()))
            values[before] = after;
          ++cursor;
          continue;
        }
        if (!degree(op))
          return false;
        if (!live.contains(&op))
          continue;
        if (isa<poly::PolynomialType>(op.getResult(0).getType()))
          continue;
        Value result;
        if (auto evaluation = dyn_cast<poly::EvaluatePolynomialOp>(op)) {
          SmallVector<Value> point;
          for (Value coordinate : evaluation.getPoint()) {
            auto actual = values.lookup(coordinate);
            if (!actual)
              return false;
            point.push_back(actual);
          }
          result = evaluate(evaluation.getPolynomial(), point);
        } else if (auto observation =
                       dyn_cast<poly::PolynomialCoefficientsOp>(op)) {
          auto entries = coefficientValues(observation.getPolynomial());
          auto width = cast<algebra::FieldArrayType>(
                           observation.getCoefficients().getType())
                           .getLength();
          if (entries.empty() || entries.size() > uint64_t(width) ||
              !check.terms.charge(width))
            return false;
          // The supported normalizer materializes the shared zero even if no
          // padding is needed. Read it explicitly, including when unused.
          auto zero = literal(scalar(observation.getPolynomial()), "0");
          if (!zero)
            return false;
          entries.resize(width, zero);
          result = pack(observation.getCoefficients().getType(), entries);
        } else if (auto domain = dyn_cast<poly::EvaluateDomainOp>(op)) {
          SmallVector<Value> entries;
          for (auto point : domain.getPoints()) {
            auto coordinate = literal(scalar(domain.getPolynomial()),
                                      cast<StringAttr>(point).getValue());
            if (!coordinate)
              return false;
            auto value = evaluate(domain.getPolynomial(), {coordinate});
            if (!value)
              return false;
            entries.push_back(value);
          }
          result = pack(domain.getValues().getType(), entries);
        } else if (auto fix = dyn_cast<poly::FixTableOp>(op)) {
          SmallVector<Value> prefix;
          for (auto coordinate : fix.getPrefix()) {
            auto actual = values.lookup(coordinate);
            if (!actual)
              return false;
            prefix.push_back(actual);
          }
          auto entries = fixTable(values.lookup(fix.getTable()), prefix);
          if (entries.empty())
            return false;
          result = pack(fix.getResult().getType(), entries);
        }
        if (!result || result.getType() != op.getResult(0).getType() || invalid)
          return false;
        values[op.getResult(0)] = result;
      }
      auto &ret = source.front().back();
      if (invalid || cursor == candidate.end() ||
          &*cursor != &candidate.back() || !check.charge(ret) ||
          !check.charge(*cursor))
        return false;
      for (auto [before, after] : zip(ret.getOperands(), cursor->getOperands()))
        if (!values.lookup(before) || values.lookup(before) != after)
          return false;
      return true;
    }
  };

  LogicalResult checkExpansion(func::FuncOp source, Block &candidate) {
    if (!interface(source, candidate))
      return refuse(source ? source.getOperation() : root,
                    "expanded interface differs");
    Expansion reader{*this, candidate.begin(), std::prev(candidate.end()), {}};
    auto outputs = reader.read(source, candidate.getArguments());
    if (failed(outputs) || reader.cursor != reader.end ||
        !charge(candidate.back()) ||
        !llvm::equal(*outputs, candidate.back().getOperands()))
      return refuse(source,
                    "actual helper substitution differs from the raw closure");
    return success();
  }
  LogicalResult checkSimplification(func::FuncOp source, Block &candidate) {
    if (!interface(source, candidate))
      return refuse(source, "simplified interface differs");
    llvm::DenseMap<Value, Value> aliases;
    llvm::DenseMap<Operation *, uint64_t> dimensions;
    auto canonical = [&](Value value) {
      auto found = aliases.find(value);
      return found == aliases.end() ? value : found->second;
    };
    // Read the supported laws without invoking folding or a producer.
    for (auto &op : source.front().without_terminator()) {
      if (!charge(op) || !flatTotal(op))
        return refuse(source, "unsupported simplification subject");
      if (auto projection = dyn_cast<algebra::ArrayAtOp>(op)) {
        auto pack = canonical(projection->getOperand(0))
                        .getDefiningOp<algebra::ArrayFromElementsOp>();
        auto index = projection.getIndexAttr().getInt();
        if (pack && index >= 0 && uint64_t(index) < pack->getNumOperands())
          aliases[projection.getResult()] = canonical(pack->getOperand(index));
      } else if (auto dimension = dyn_cast<data::DimOp>(op)) {
        auto type =
            dyn_cast<CollectionTypeInterface>(dimension.getInput().getType());
        auto extent =
            type ? type.getStaticExtent(dimension.getAxisAttr().getInt())
                 : std::nullopt;
        if (extent)
          dimensions[&op] = *extent;
      }
    }
    llvm::DenseSet<Value> needed;
    llvm::DenseSet<Operation *> retained;
    for (Value value : source.front().back().getOperands())
      needed.insert(canonical(value));
    for (auto &op : llvm::reverse(source.front().without_terminator())) {
      if (!charge(op))
        return refuse(source, "simplification liveness work bound");
      if (op.getNumResults() == 1 && aliases.contains(op.getResult(0)))
        continue;
      bool live = finite::isComputation(&op) ||
                  llvm::any_of(op.getResults(),
                               [&](Value v) { return needed.contains(v); });
      if (!live)
        continue;
      retained.insert(&op);
      if (!dimensions.contains(&op))
        for (Value value : op.getOperands())
          needed.insert(canonical(value));
    }
    llvm::DenseMap<Value, Value> values;
    for (auto [a, b] :
         llvm::zip(source.getArguments(), candidate.getArguments()))
      values[a] = b;
    auto cursor = candidate.begin();
    auto end = std::prev(candidate.end());
    for (auto &op : source.front().without_terminator()) {
      if (!retained.contains(&op))
        continue;
      if (cursor == end || !charge(*cursor))
        return refuse(source, "missing live simplified instruction");
      auto &actual = *cursor++;
      if (auto found = dimensions.find(&op); found != dimensions.end()) {
        auto index = dyn_cast<data::IndexOp>(actual);
        if (!index || actual.getResultTypes() != op.getResultTypes() ||
            index.getValue() != std::to_string(found->second))
          return refuse(source, "static dimension constant differs");
      } else {
        if (!sameShape(op, actual))
          return refuse(source, "live concrete instruction changed");
        for (auto [a, b] : llvm::zip(op.getOperands(), actual.getOperands()))
          if (values.lookup(canonical(a)) != b)
            return refuse(source, "simplified operand differs");
      }
      for (auto [a, b] : llvm::zip(op.getResults(), actual.getResults()))
        values[a] = b;
    }
    if (cursor != end || !charge(*cursor))
      return refuse(source, "extra simplified instruction");
    for (auto [a, b] :
         llvm::zip(source.front().back().getOperands(), cursor->getOperands()))
      if (values.lookup(canonical(a)) != b)
        return refuse(source, "simplified return differs");
    return success();
  }
  LogicalResult checkNormalization(func::FuncOp source, Block &candidate,
                                   SmallVectorImpl<Operation *> *generated) {
    if (!interface(source, candidate))
      return refuse(source ? source.getOperation() : root,
                    "normalized interface differs");
    Normalization reader(*this, source, candidate);
    if (!reader.run())
      return refuse(
          source,
          "concrete occurrences or polynomial realization trace differ");
    if (failed(meaning.check(source, candidate)))
      return failure();
    if (generated)
      append_range(*generated, reader.generated);
    return success();
  }
};

NormalizationProvenanceChecker::NormalizationProvenanceChecker(Operation *root,
                                                               size_t work)
    : implementation(std::make_unique<Implementation>(root, work)) {}
NormalizationProvenanceChecker::~NormalizationProvenanceChecker() = default;
LogicalResult
NormalizationProvenanceChecker::checkExpansion(func::FuncOp source,
                                               Block &candidate) {
  return implementation->checkExpansion(source, candidate);
}
LogicalResult
NormalizationProvenanceChecker::checkSimplification(func::FuncOp source,
                                                    Block &candidate) {
  return implementation->checkSimplification(source, candidate);
}
LogicalResult NormalizationProvenanceChecker::checkNormalization(
    func::FuncOp expanded, Block &candidate,
    SmallVectorImpl<Operation *> *generated) {
  return implementation->checkNormalization(expanded, candidate, generated);
}
} // namespace zkc::kernel
