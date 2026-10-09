#include "zkc/Contracts/RingExpression.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <map>

using namespace llvm;
using namespace zkc::ring;
using N = Node;
static constexpr uint64_t prime = 2130706433;
static constexpr const char *base = "koala-bear";
static constexpr const char *extension = "koala-bear.ext8-binomial3";

static void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> static T value(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
template <typename T> static void refuses(Expected<T> result, StringRef code) {
  require(!result, "expected refusal");
  auto actual = toString(result.takeError());
  if (actual != code)
    errs() << actual << " != " << code << '\n';
  require(actual == code, "wrong refusal");
}

// Independent coefficient arithmetic. Scalar substitution is the constant
// subring, so both interpretations exercise exactly the same admitted DAG.
using Polynomial = std::vector<uint64_t>;
struct Algebra {
  std::vector<Polynomial> inputs;
  std::map<uint32_t, unsigned> reads;
  Expected<Polynomial> input(uint32_t i, StringRef field) {
    require(field == base, "test provider only supports the prime field");
    ++reads[i];
    if (i >= inputs.size())
      return zkc::error("test-missing-input");
    return inputs[i];
  }
  Expected<Polynomial> constant(StringRef field, StringRef literal) {
    require(field == base, "constant field");
    return Polynomial{std::stoull(literal.str())};
  }
  Expected<Polynomial> add(StringRef, const Polynomial &a,
                           const Polynomial &b) {
    Polynomial result(std::max(a.size(), b.size()), 0);
    for (size_t i = 0; i < result.size(); ++i)
      result[i] =
          ((i < a.size() ? a[i] : 0) + (i < b.size() ? b[i] : 0)) % prime;
    return result;
  }
  Expected<Polynomial> mul(StringRef, const Polynomial &a,
                           const Polynomial &b) {
    Polynomial result(a.size() + b.size() - 1, 0);
    for (size_t i = 0; i < a.size(); ++i)
      for (size_t j = 0; j < b.size(); ++j)
        result[i + j] = (result[i + j] + a[i] * b[j]) % prime;
    return result;
  }
  Expected<Polynomial> neg(StringRef, const Polynomial &a) {
    Polynomial result;
    for (auto x : a)
      result.push_back((prime - x) % prime);
    return result;
  }
  Expected<Polynomial> embed(StringRef, StringRef, const Polynomial &) {
    return zkc::error("test-no-extension-provider");
  }
};

int main() {
  auto expression = value(
      Expression::create({{base}, {base}},
                         {N::slot(0), N::slot(1), N::mul(0, 1),
                          N::literal(base, "3"), N::add(2, 3), N::add(0, 1)},
                         {4, 5}));
  require(expression.facts()[4].degree == 2 &&
              expression.facts()[5].degree == 1,
          "per-output formal degree");
  Algebra scalar{{{5}, {11}}, {}};
  auto scalarResult = value(expression.evaluate<Polynomial>({0, 1}, scalar));
  require(scalarResult == std::vector<Polynomial>{{58}, {16}},
          "scalar outputs");
  require(scalar.reads == std::map<uint32_t, unsigned>{{0, 1}, {1, 1}},
          "shared input read once");
  Algebra coefficients{{{1, 2}, {3, 4}}, {}};
  auto polynomialResult =
      value(expression.evaluate<Polynomial>({0, 1}, coefficients));
  require(polynomialResult == std::vector<Polynomial>{{6, 10, 8}, {4, 6}},
          "exact product degree retained, not pointwise-table interpolation");
  auto encoded = zkc::printJson(expression.encode());
  auto decoded = value(readExpressionText(encoded));
  require(decoded.identity() == expression.identity() &&
              zkc::printJson(decoded.encode()) == encoded,
          "canonical identity round trip");
  require(value(expression.usedInputs({1})) == std::vector<uint32_t>{0, 1},
          "selected output support");

  auto selective = value(Expression::create(
      {{base}, {base}}, {N::slot(0), N::slot(1), N::slot(0), N::add(0, 2)},
      {3, 1}));
  Algebra partial{{{7}}, {}};
  require(value(selective.evaluate<Polynomial>({0, 0}, partial)) ==
                  std::vector<Polynomial>{{14}, {14}} &&
              partial.reads[0] == 1 && partial.reads.count(1) == 0,
          "unselected output neither reads missing slot nor duplicates input");
  refuses(selective.evaluate<Polynomial>({1}, partial), "test-missing-input");
  refuses(selective.usedInputs({2}), "ring-output");

  auto mixed = value(Expression::create(
      {{base}, {extension}},
      {N::slot(0), N::embed(extension, 0), N::slot(1), N::mul(1, 2)}, {3}));
  require(mixed.facts()[3].field == extension && mixed.facts()[3].degree == 2,
          "explicit mixed-field embedding and degree");
  refuses(Expression::create({{base}, {extension}},
                             {N::slot(0), N::slot(1), N::mul(0, 1)}, {2}),
          "ring-field-mismatch");
  refuses(
      Expression::create({{extension}}, {N::slot(0), N::embed(base, 0)}, {1}),
      "ring-embedding");
  refuses(Expression::create({}, {N::literal(base, "2130706433")}, {0}),
          "ring-literal");
  refuses(Expression::create({}, {N::literal(base, "01")}, {0}),
          "ring-literal");
  refuses(Expression::create({}, {N::literal("missing-field", "0")}, {0}),
          "ring-field");
  refuses(Expression::create({{base}}, {N::slot(1)}, {0}), "ring-input");
  refuses(Expression::create({{base}}, {N::slot(0), N::mul(0, 2)}, {1}),
          "ring-edge");
  refuses(Expression::create({{base}}, {N::slot(0)}, {1}), "ring-output");
  refuses(
      Expression::create({{base}}, {N::slot(0), N::literal(base, "0")}, {0}),
      "ring-unreachable-node");
  refuses(expression.degrees({Limits::degree, 1}), "ring-degree");
  require(value(expression.degrees({0, 7}))[4] == 7, "view-specific weights");
  auto empty = value(Expression::create({}, {}, {}));
  require(value(empty.usedInputs({})).empty(), "empty conjunction");
  std::vector<N> deep{N::literal(base, "1")};
  for (uint32_t i = 0; i < Limits::depth; ++i)
    deep.push_back(N::neg(i));
  refuses(Expression::create({}, std::move(deep), {Limits::depth}),
          "ring-depth");
  auto malformed = N::slot(0);
  malformed.constant = "7";
  refuses(Expression::create({{base}}, {malformed}, {0}), "ring-node-shape");
  refuses(readExpressionText("[\"zkc.ring/1\",[],[],[]]"), "ring-schema");
  refuses(
      readExpressionText(
          "[\"zkc.ring/0\",[],[[\"constant\",\"koala-bear\",\"0\"]],[0.0]]"),
      "ring-schema");
  refuses(
      readExpressionText(
          "[\"zkc.ring/0\",[],[[\"constant\",\"koala-bear\",\"0\",0]],[0]]"),
      "ring-schema");
  refuses(readExpressionText(std::string(Limits::bytes + 1, ' ')),
          "ring-limit");
  outs() << "ring expression admission and independent substitution checks "
            "passed\n";
}
