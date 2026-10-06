#include "MathematicalValues.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
using Term = ValueCorrespondence::Term;
// Definitional polynomial laws over symbolic scalar terms. No MLIR is emitted,
// and no producer expansion or degree analysis is called. Interpolation weights
// come from solving the Vandermonde system, independently of the producer's
// Lagrange-basis construction.
class PolynomialValues {
  ValueCorrespondence &terms;
  llvm::DenseMap<unsigned, unsigned> &normal;
  Builder builder;
  unsigned depth = 0;
  bool fixings;
  std::map<std::pair<Term, std::vector<Term>>, Term> &evaluations;
  llvm::DenseMap<Term, SmallVector<Term>> &coefficientCache;
  bool enter() { return depth++ < 128 && terms.charge(); }
  Term make(StringRef name, Type type, ArrayRef<Term> inputs = {},
            DictionaryAttr attributes = {}) {
    if (!attributes)
      attributes = builder.getDictionaryAttr({});
    return terms.expression(name, type, attributes, inputs);
  }
  algebra::FieldType field(Term polynomial) {
    return algebra::FieldType::get(
        builder.getContext(),
        cast<poly::PolynomialType>(terms.expression(polynomial).type)
            .getDomain());
  }
  Term literal(algebra::FieldType type, StringRef number) {
    if (!algebra::isCanonicalFieldLiteral(type.getDomain(), number))
      return 0;
    return make("algebra.constant", type, {},
                builder.getDictionaryAttr({builder.getNamedAttr(
                    "value", builder.getStringAttr(number))}));
  }
  Term binary(StringRef name, Term a, Term b) {
    if (!a || !b)
      return 0;
    return make(name, terms.expression(a).type, {a, b});
  }
  Term add(Term a, Term b) { return binary("algebra.field_add", a, b); }
  Term multiply(Term a, Term b) {
    return binary("algebra.field_multiply", a, b);
  }
  Term subtract(Term a, Term b) {
    return binary("algebra.field_subtract", a, b);
  }
  Term at(Term array, unsigned index) {
    if (!array)
      return 0;
    auto node = terms.expression(array);
    auto type = dyn_cast<RankedTensorType>(node.type);
    if (!type || type.getRank() != 1 || index >= type.getDimSize(0))
      return 0;
    if (node.name && node.name.getValue() == "tensor.from_elements")
      return node.operands[index];
    return make("algebra.array_at", type.getElementType(), {array},
                builder.getDictionaryAttr({builder.getNamedAttr(
                    "index", builder.getI64IntegerAttr(index))}));
  }
  SmallVector<Term> unpack(Term array) {
    if (!array)
      return {};
    auto type = dyn_cast<RankedTensorType>(terms.expression(array).type);
    if (!type || type.getRank() != 1 || type.isDynamicDim(0) ||
        !terms.charge(type.getDimSize(0)))
      return {};
    SmallVector<Term> values;
    for (int64_t i = 0; i < type.getDimSize(0); ++i)
      values.push_back(at(array, i));
    return values;
  }
  SmallVector<Term> tablePrefix(Term table, ArrayRef<Term> point) {
    auto values = unpack(table);
    for (Term x : point) {
      if (values.size() < 2 || values.size() % 2 ||
          !terms.charge(values.size()))
        return {};
      SmallVector<Term> next;
      unsigned half = values.size() / 2;
      for (unsigned i = 0; i < half; ++i)
        next.push_back(
            add(values[i], multiply(x, subtract(values[i + half], values[i]))));
      values = std::move(next);
    }
    return values;
  }
  Term horner(ArrayRef<Term> coefficients, Term point) {
    if (coefficients.empty())
      return 0;
    Term result = coefficients.back();
    for (auto c : llvm::reverse(coefficients.drop_back()))
      result = add(multiply(result, point), c);
    return result;
  }
  SmallVector<unsigned> degrees(Term polynomial) {
    if (!enter()) {
      --depth;
      return {};
    }
    auto leave = llvm::scope_exit([&] { --depth; });
    auto node = terms.expression(polynomial);
    auto type = cast<poly::PolynomialType>(node.type);
    if (!node.name)
      return {};
    StringRef name = node.name.getValue();
    if (name == "poly.constant")
      return SmallVector<unsigned>(type.getArity(), 0);
    if (name == "poly.mle")
      return SmallVector<unsigned>(type.getArity(), 1);
    if (name == "poly.from_coefficients")
      return {unsigned(
          cast<RankedTensorType>(terms.expression(node.operands[0]).type)
              .getDimSize(0) -
          1)};
    if (name == "poly.interpolate")
      return {unsigned(node.attributes.getAs<ArrayAttr>("points").size() - 1)};
    auto a = degrees(node.operands[0]);
    if (name == "poly.fix") {
      unsigned prefix = node.operands.size() - 1;
      if (a.size() < prefix)
        return {};
      return SmallVector<unsigned>(a.begin() + prefix, a.end());
    }
    if (name == "poly.sum_suffix") {
      unsigned suffix = node.attributes.getAs<IntegerAttr>("count").getInt();
      if (a.size() < suffix)
        return {};
      a.resize(a.size() - suffix);
      return a;
    }
    if (name == "poly.add" || name == "poly.multiply") {
      auto b = degrees(node.operands[1]);
      if (a.size() != b.size())
        return {};
      for (auto [x, y] : zip(a, b)) {
        if (name == "poly.add")
          x = std::max(x, y);
        else {
          if (x > 1000000 - y)
            return {};
          x += y;
        }
      }
      return a;
    }
    return {};
  }
  SmallVector<Term> interpolate(ArrayRef<Term> values, ArrayAttr points,
                                algebra::FieldType type) {
    unsigned n = values.size();
    if (!n || n > 64 || n != points.size() || !terms.charge(n * n * 2))
      return {};
    StringRef decimal = protocol::fieldModulus(type.getDomain());
    if (decimal.empty() || !protocol::installedDomains().hasFact(
                               "PrimeField", {type.getDomain().str()}))
      return {};
    unsigned width = 2 * APInt::getBitsNeeded(decimal, 10) + 2;
    APInt modulus(width, decimal, 10), zero(width, 0), one(width, 1);
    SmallVector<SmallVector<APInt>> matrix;
    for (unsigned row = 0; row < n; ++row) {
      auto spelling = cast<StringAttr>(points[row]).getValue();
      if (!algebra::isCanonicalFieldLiteral(type.getDomain(), spelling) ||
          !all_of(spelling, [](char c) { return c >= '0' && c <= '9'; }))
        return {};
      APInt x(width, spelling, 10), power = one;
      SmallVector<APInt> line(2 * n, zero);
      for (unsigned column = 0; column < n; ++column) {
        line[column] = power;
        power = (power * x).urem(modulus);
      }
      line[n + row] = one;
      matrix.push_back(std::move(line));
    }
    for (unsigned column = 0; column < n; ++column) {
      unsigned pivot = column;
      while (pivot < n && matrix[pivot][column].isZero())
        ++pivot;
      if (pivot == n || !terms.charge(width + 2 * n))
        return {};
      std::swap(matrix[pivot], matrix[column]);
      // Extended Euclid with coefficients reduced modulo p. Intermediate
      // products fit the selected double-width unsigned representation.
      APInt r = modulus, nextR = matrix[column][column];
      APInt inverse = zero, nextInverse = one;
      while (!nextR.isZero()) {
        if (!terms.charge())
          return {};
        APInt quotient = r.udiv(nextR), remainder = r.urem(nextR);
        APInt coefficient =
            (inverse + modulus - (quotient * nextInverse).urem(modulus))
                .urem(modulus);
        r = nextR;
        nextR = remainder;
        inverse = nextInverse;
        nextInverse = coefficient;
      }
      if (r != one)
        return {};
      for (auto &entry : matrix[column])
        entry = (entry * inverse).urem(modulus);
      for (unsigned row = 0; row < n; ++row) {
        if (row == column)
          continue;
        if (!terms.charge(2 * n))
          return {};
        auto scale = matrix[row][column];
        for (unsigned k = 0; k < 2 * n; ++k)
          matrix[row][k] = (matrix[row][k] + modulus -
                            (scale * matrix[column][k]).urem(modulus))
                               .urem(modulus);
      }
    }
    SmallVector<Term> result(n, literal(type, "0"));
    for (unsigned degree = 0; degree < n; ++degree)
      for (unsigned sample = 0; sample < n; ++sample) {
        SmallString<128> weight;
        matrix[degree][n + sample].toString(weight, 10, false);
        result[degree] = add(result[degree],
                             multiply(literal(type, weight), values[sample]));
      }
    return result;
  }
  SmallVector<Term> coefficients(Term polynomial) {
    if (auto found = coefficientCache.find(polynomial);
        found != coefficientCache.end())
      return found->second;
    if (!enter()) {
      --depth;
      return {};
    }
    auto leave = llvm::scope_exit([&] { --depth; });
    auto node = terms.expression(polynomial);
    if (!node.name)
      return {};
    StringRef name = node.name.getValue();
    SmallVector<Term> result;
    if (name == "poly.from_coefficients")
      result = unpack(node.operands[0]);
    else if (name == "poly.constant")
      result = {node.operands[0]};
    else if (name == "poly.interpolate")
      result = interpolate(unpack(node.operands[0]),
                           node.attributes.getAs<ArrayAttr>("points"),
                           field(polynomial));
    else if (name == "poly.add" || name == "poly.multiply") {
      auto a = coefficients(node.operands[0]),
           b = coefficients(node.operands[1]);
      if (a.empty() || b.empty())
        return {};
      bool product = name == "poly.multiply";
      size_t size =
          product ? a.size() + b.size() - 1 : std::max(a.size(), b.size());
      if (!terms.charge(size) ||
          (product && !terms.charge(a.size() * b.size())))
        return {};
      Term zero = literal(field(polynomial), "0");
      result.assign(size, zero);
      if (product) {
        for (unsigned i = 0; i < a.size(); ++i)
          for (unsigned j = 0; j < b.size(); ++j)
            result[i + j] = add(result[i + j], multiply(a[i], b[j]));
      } else
        for (unsigned i = 0; i < size; ++i)
          result[i] =
              add(i < a.size() ? a[i] : zero, i < b.size() ? b[i] : zero);
    } else {
      auto bound = degrees(polynomial);
      if (bound.size() != 1 || bound[0] >= 64)
        return {};
      SmallVector<Attribute> points;
      SmallVector<Term> samples;
      for (unsigned i = 0; i <= bound[0]; ++i) {
        auto point = std::to_string(i);
        points.push_back(builder.getStringAttr(point));
        samples.push_back(
            evaluate(polynomial, {literal(field(polynomial), point)}));
      }
      result =
          interpolate(samples, builder.getArrayAttr(points), field(polynomial));
    }
    if (is_contained(result, Term(0)))
      return {};
    coefficientCache[polynomial] = result;
    return result;
  }
  Term evaluate(Term polynomial, ArrayRef<Term> point) {
    auto key = std::make_pair(polynomial,
                              std::vector<Term>(point.begin(), point.end()));
    if (auto found = evaluations.find(key); found != evaluations.end())
      return found->second;
    if (!enter()) {
      --depth;
      return 0;
    }
    auto leave = llvm::scope_exit([&] { --depth; });
    auto node = terms.expression(polynomial);
    if (!node.name)
      return 0;
    StringRef name = node.name.getValue();
    Term result = 0;
    if (name == "poly.constant")
      result = node.operands[0];
    else if (name == "poly.from_coefficients" || name == "poly.interpolate") {
      if (point.size() != 1)
        return 0;
      result = horner(coefficients(polynomial), point[0]);
    } else if (name == "poly.mle") {
      auto values = tablePrefix(node.operands[0], point);
      if (values.size() == 1)
        result = values[0];
    } else if (name == "poly.add" || name == "poly.multiply") {
      auto a = evaluate(node.operands[0], point),
           b = evaluate(node.operands[1], point);
      result = name == "poly.add" ? add(a, b) : multiply(a, b);
    } else if (name == "poly.fix") {
      SmallVector<Term> coordinates(node.operands.begin() + 1,
                                    node.operands.end());
      append_range(coordinates, point);
      result = evaluate(node.operands[0], coordinates);
    } else if (name == "poly.sum_suffix") {
      auto count = node.attributes.getAs<IntegerAttr>("count").getInt();
      if (count < 0 || count >= 63 || !terms.charge(uint64_t(1) << count))
        return 0;
      auto zero = literal(field(polynomial), "0"),
           one = literal(field(polynomial), "1");
      result = zero;
      for (uint64_t assignment = 0; assignment < (uint64_t(1) << count);
           ++assignment) {
        SmallVector<Term> coordinates(point);
        for (int64_t axis = count; axis-- > 0;)
          coordinates.push_back((assignment >> axis) & 1 ? one : zero);
        result = add(result, evaluate(node.operands[0], coordinates));
        if (!result)
          return 0;
      }
    }
    evaluations[key] = result;
    return result;
  }
  Term fix(Term polynomial, ArrayRef<Term> prefix) {
    if (prefix.empty())
      return polynomial;
    if (!enter()) {
      --depth;
      return 0;
    }
    auto leave = llvm::scope_exit([&] { --depth; });
    auto node = terms.expression(polynomial);
    auto original = cast<poly::PolynomialType>(node.type);
    if (prefix.size() > original.getArity())
      return 0;
    auto type =
        poly::PolynomialType::get(builder.getContext(), original.getDomain(),
                                  original.getArity() - prefix.size());
    StringRef name = node.name ? node.name.getValue() : StringRef();
    if (name == "poly.add" || name == "poly.multiply")
      return make(
          name, type,
          {fix(node.operands[0], prefix), fix(node.operands[1], prefix)});
    if (name == "poly.constant")
      return make(name, type, node.operands);
    if (name == "poly.mle") {
      if (type.getArity() >= 63)
        return 0;
      auto table = RankedTensorType::get(
          {int64_t(uint64_t(1) << type.getArity())}, field(polynomial));
      SmallVector<Term> inputs{node.operands[0]};
      append_range(inputs, prefix);
      return make("poly.mle", type, {make("poly.fix_table", table, inputs)});
    }
    if (name == "poly.fix") {
      SmallVector<Term> full(node.operands.begin() + 1, node.operands.end());
      append_range(full, prefix);
      return fix(node.operands[0], full);
    }
    SmallVector<Term> inputs{polynomial};
    append_range(inputs, prefix);
    return make("poly.fix", type, inputs);
  }
  Term observation(const ValueCorrespondence::Expression &node,
                   ArrayRef<Term> inputs) {
    StringRef name = node.name.getValue();
    if (fixings) {
      if (name == "poly.fix")
        return fix(inputs[0], inputs.drop_front());
      return terms.expression(name, node.type, node.attributes, inputs,
                              node.coordinate);
    }
    if (name == "poly.evaluate")
      return evaluate(inputs[0], inputs.drop_front());
    if (name == "poly.coefficients") {
      auto values = coefficients(inputs[0]);
      unsigned size = cast<RankedTensorType>(node.type).getDimSize(0);
      if (values.empty() || values.size() > size || !terms.charge(size))
        return 0;
      values.resize(size, literal(field(inputs[0]), "0"));
      return make("tensor.from_elements", node.type, values);
    }
    if (name == "poly.evaluate_domain") {
      SmallVector<Term> values;
      for (auto point : node.attributes.getAs<ArrayAttr>("points"))
        values.push_back(evaluate(
            inputs[0],
            {literal(field(inputs[0]), cast<StringAttr>(point).getValue())}));
      return make("tensor.from_elements", node.type, values);
    }
    if (name == "poly.fix_table") {
      auto values = tablePrefix(inputs[0], inputs.drop_front());
      if (values.empty())
        return 0;
      return make("tensor.from_elements", node.type, values);
    }
    if (name == "algebra.array_at")
      return at(inputs[0],
                node.attributes.getAs<IntegerAttr>("index").getInt());
    return terms.expression(name, node.type, node.attributes, inputs,
                            node.coordinate);
  }

public:
  PolynomialValues(ValueCorrespondence &terms, PolynomialValueCache &cache,
                   MLIRContext *context, bool fixings = false)
      : terms(terms), normal(cache.normal), builder(context), fixings(fixings),
        evaluations(cache.evaluations), coefficientCache(cache.coefficients) {}
  Term normalize(Term root) {
    SmallVector<Term> pending{root};
    while (!pending.empty()) {
      if (!terms.charge())
        return 0;
      Term current = pending.back();
      if (normal.contains(current)) {
        pending.pop_back();
        continue;
      }
      auto node = terms.expression(current);
      if (!node.name) {
        normal[current] = current;
        pending.pop_back();
        continue;
      }
      bool ready = true;
      for (Term input : node.operands) {
        if (!terms.charge())
          return 0;
        if (!normal.contains(input)) {
          pending.push_back(input);
          ready = false;
        }
      }
      if (!ready)
        continue;
      SmallVector<Term> inputs;
      for (Term input : node.operands)
        inputs.push_back(normal.lookup(input));
      Term result = observation(node, inputs);
      if (!result)
        return 0;
      normal[current] = result;
      pending.pop_back();
    }
    return normal.lookup(root);
  }
};
} // namespace
ValueCorrespondence::Term
normalizePolynomialFixings(ValueCorrespondence &terms, Term value,
                           PolynomialValueCache &cache) {
  return PolynomialValues(terms, cache,
                          terms.expression(value).type.getContext(), true)
      .normalize(value);
}
ValueCorrespondence::Term
normalizePolynomialValues(ValueCorrespondence &terms, Term value,
                          PolynomialValueCache &cache) {
  return PolynomialValues(terms, cache,
                          terms.expression(value).type.getContext())
      .normalize(value);
}
} // namespace zkc::mathematical
