#include "zkc/Contracts/RingSharing.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <map>
#include <numeric>

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
static void accepts(Error error, StringRef message) {
  if (error) {
    errs() << message << ": " << toString(std::move(error)) << '\n';
    std::exit(1);
  }
}
static void refuses(Error error, StringRef code) {
  require(bool(error), "expected refusal");
  auto actual = toString(std::move(error));
  if (actual != code)
    errs() << actual << " != " << code << '\n';
  require(actual == code, "wrong refusal");
}

// Coefficient vectors over the prime field; scalars are the length-one case.
// Every declared field is interpreted in this one ring and an explicit
// embedding is the identity map, which is one admissible choice of algebra
// and compatible field maps for comparing two arenas.
using Polynomial = std::vector<uint64_t>;
static Polynomial addP(const Polynomial &a, const Polynomial &b) {
  Polynomial result(std::max(a.size(), b.size()), 0);
  for (size_t i = 0; i < result.size(); ++i)
    result[i] = ((i < a.size() ? a[i] : 0) + (i < b.size() ? b[i] : 0)) % prime;
  return result;
}
static Polynomial mulP(const Polynomial &a, const Polynomial &b) {
  Polynomial result(a.size() + b.size() - 1, 0);
  for (size_t i = 0; i < a.size(); ++i)
    for (size_t j = 0; j < b.size(); ++j)
      result[i + j] = (result[i + j] + a[i] * b[j]) % prime;
  return result;
}
static Polynomial negP(const Polynomial &a) {
  Polynomial result;
  for (auto x : a)
    result.push_back((prime - x) % prime);
  return result;
}

// Independent reference: a memoized walk over the node list that never calls
// Expression::evaluate. Each node is computed once in index order.
static std::vector<Polynomial> reference(const Expression &expression,
                                         ArrayRef<Polynomial> assignment) {
  std::vector<Polynomial> values;
  for (const auto &node : expression.nodes()) {
    switch (node.kind) {
    case Kind::Constant:
      values.push_back({std::stoull(node.constant)});
      break;
    case Kind::Input:
      values.push_back(assignment[node.input]);
      break;
    case Kind::Add:
      values.push_back(addP(values[node.left], values[node.right]));
      break;
    case Kind::Mul:
      values.push_back(mulP(values[node.left], values[node.right]));
      break;
    case Kind::Neg:
      values.push_back(negP(values[node.left]));
      break;
    case Kind::Embed:
      values.push_back(values[node.left]);
      break;
    }
  }
  std::vector<Polynomial> result;
  for (auto output : expression.outputs())
    result.push_back(values[output]);
  return result;
}

// The algebra handed to Expression::evaluate, counting what it is asked.
struct Algebra {
  std::vector<Polynomial> inputs;
  std::map<uint32_t, unsigned> reads;
  unsigned operations = 0;
  Expected<Polynomial> input(uint32_t i, StringRef) {
    ++reads[i];
    if (i >= inputs.size())
      return zkc::error("test-missing-input");
    return inputs[i];
  }
  Expected<Polynomial> constant(StringRef, StringRef literal) {
    return Polynomial{std::stoull(literal.str())};
  }
  Expected<Polynomial> add(StringRef, const Polynomial &a,
                           const Polynomial &b) {
    ++operations;
    return addP(a, b);
  }
  Expected<Polynomial> mul(StringRef, const Polynomial &a,
                           const Polynomial &b) {
    ++operations;
    return mulP(a, b);
  }
  Expected<Polynomial> neg(StringRef, const Polynomial &a) {
    ++operations;
    return negP(a);
  }
  Expected<Polynomial> embed(StringRef source, StringRef target,
                             const Polynomial &a) {
    require(source == base && target == extension, "installed embedding");
    ++operations;
    return a;
  }
};

static std::vector<uint32_t> allPositions(const Expression &expression) {
  std::vector<uint32_t> positions(expression.outputs().size());
  std::iota(positions.begin(), positions.end(), 0);
  return positions;
}

// Everything the checker's judgment is documented to imply, verified directly
// on the two arenas rather than trusted from the structural check.
static void agree(const Expression &original, const Sharing &sharing,
                  ArrayRef<uint32_t> weights,
                  ArrayRef<std::vector<Polynomial>> assignments) {
  const auto &shared = sharing.expression;
  accepts(checkSharing(original, shared, sharing.nodeMap), "sharing judgment");
  require(shared.inputs().size() == original.inputs().size(),
          "input declarations kept");
  for (size_t i = 0; i < original.inputs().size(); ++i)
    require(shared.inputs()[i].field == original.inputs()[i].field,
            "input fields kept in order");
  auto originalDegrees = value(original.degrees(weights));
  auto sharedDegrees = value(shared.degrees(weights));
  for (uint32_t i = 0; i < original.nodes().size(); ++i) {
    uint32_t image = sharing.nodeMap[i];
    require(shared.facts()[image].field == original.facts()[i].field,
            "field fact kept");
    require(shared.facts()[image].degree == original.facts()[i].degree &&
                shared.facts()[image].depth == original.facts()[i].depth,
            "formation degree and depth kept");
    require(sharedDegrees[image] == originalDegrees[i], "weighted degree kept");
  }
  require(shared.outputs().size() == original.outputs().size(),
          "output count kept");
  for (uint32_t p = 0; p < original.outputs().size(); ++p)
    require(value(shared.usedInputs({p})) == value(original.usedInputs({p})),
            "used inputs kept per output position");
  auto positions = allPositions(original);
  for (const auto &assignment : assignments) {
    Algebra algebra{assignment, {}, 0};
    auto evaluated = value(shared.evaluate<Polynomial>(positions, algebra));
    require(evaluated == reference(original, assignment),
            "shared evaluation agrees with the independent reference");
    require(reference(shared, assignment) == evaluated,
            "reference agrees on the shared arena");
    for (uint32_t input : value(original.usedInputs(positions)))
      require(algebra.reads[input] == 1, "each used input read once");
    require(algebra.reads.size() ==
                value(original.usedInputs(positions)).size(),
            "no unused input read");
  }
  require(sharing.changed == (shared.identity() != original.identity()),
          "identity changes exactly when the representation changes");
  auto again = value(shareExpression(shared));
  require(!again.changed && again.expression.identity() == shared.identity(),
          "sharing is idempotent");
  for (uint32_t i = 0; i < again.nodeMap.size(); ++i)
    require(again.nodeMap[i] == i, "idempotent map is the identity");
}

int main() {
  // x*y + x*y built twice, a repeated literal, repeated negations, an unused
  // declared input and a repeated output position.
  auto original = value(Expression::create(
      {{base}, {base}, {base}},
      {N::slot(0), N::slot(1), N::mul(0, 1), N::slot(0), N::slot(1),
       N::mul(3, 4), N::add(2, 5), N::literal(base, "3"), N::literal(base, "3"),
       N::mul(6, 7), N::add(8, 9), N::neg(2), N::neg(5), N::add(11, 12)},
      {10, 13, 10, 6}));
  auto sharing = value(shareExpression(original));
  require(sharing.nodeMap ==
              std::vector<uint32_t>{0, 1, 2, 0, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8},
          "first occurrence owns each shared node");
  require(sharing.expression.nodes().size() == 9 && sharing.changed,
          "identical nodes merged");
  require(sharing.expression.outputs() == ArrayRef<uint32_t>({6, 8, 6, 3}),
          "ordered outputs with the duplicate kept");
  require(sharing.expression.inputs().size() == 3 &&
              value(sharing.expression.usedInputs({0, 1, 2, 3})) ==
                  std::vector<uint32_t>{0, 1},
          "unused declared input kept and still unused");
  agree(original, sharing, {0, 7, 2},
        {{{5}, {11}, {0}}, {{1, 2}, {3, 4}, {9}}});
  Algebra scalar{{{5}, {11}}, {}, 0};
  require(
      value(sharing.expression.evaluate<Polynomial>({0, 1, 2, 3}, scalar)) ==
          std::vector<Polynomial>{{333}, {prime - 110}, {333}, {110}},
      "absolute values");
  Algebra before{{{5}, {11}}, {}, 0};
  (void)value(original.evaluate<Polynomial>({0, 1, 2, 3}, before));
  require(before.operations == 8 && scalar.operations == 6,
          "the shared arena performs fewer operations");

  // Candidates the judgment must reject, all with admitted arenas.
  const auto &shared = sharing.expression;
  auto map = sharing.nodeMap;
  auto wrong = map;
  wrong[3] = 1; // x remapped to y: same kind, different slot
  refuses(checkSharing(original, shared, wrong), "ring-sharing-node");
  wrong = map;
  wrong[6] = 6; // an addition remapped to another addition
  refuses(checkSharing(original, shared, wrong), "ring-sharing-node");
  auto swapped = value(
      Expression::create({{base}, {base}, {base}},
                         {N::slot(0), N::slot(1), N::mul(1, 0), N::add(2, 2),
                          N::literal(base, "3"), N::mul(3, 4), N::add(4, 5),
                          N::neg(2), N::add(7, 7)},
                         {6, 8, 6, 3}));
  refuses(checkSharing(original, swapped, map), "ring-sharing-node");
  auto reordered = value(
      Expression::create({{base}, {base}, {base}},
                         {N::slot(0), N::slot(1), N::mul(0, 1), N::add(2, 2),
                          N::literal(base, "3"), N::mul(3, 4), N::add(4, 5),
                          N::neg(2), N::add(7, 7)},
                         {8, 6, 6, 3}));
  refuses(checkSharing(original, reordered, map), "ring-sharing-outputs");
  auto deduplicated = value(
      Expression::create({{base}, {base}, {base}},
                         {N::slot(0), N::slot(1), N::mul(0, 1), N::add(2, 2),
                          N::literal(base, "3"), N::mul(3, 4), N::add(4, 5),
                          N::neg(2), N::add(7, 7)},
                         {6, 8, 3}));
  refuses(checkSharing(original, deduplicated, map), "ring-sharing-outputs");
  auto dropped = value(
      Expression::create({{base}, {base}},
                         {N::slot(0), N::slot(1), N::mul(0, 1), N::add(2, 2),
                          N::literal(base, "3"), N::mul(3, 4), N::add(4, 5),
                          N::neg(2), N::add(7, 7)},
                         {6, 8, 6, 3}));
  refuses(checkSharing(original, dropped, map), "ring-sharing-inputs");
  refuses(checkSharing(original, shared, ArrayRef<uint32_t>(map).drop_back()),
          "ring-sharing-map");
  wrong = map;
  wrong[13] = 9;
  refuses(checkSharing(original, shared, wrong), "ring-sharing-map");

  // Algebraic rewrites are not sharing: a product by zero keeps its read.
  auto zeroed = value(Expression::create(
      {{base}}, {N::slot(0), N::literal(base, "0"), N::mul(0, 1)}, {2}));
  auto zeroSharing = value(shareExpression(zeroed));
  require(!zeroSharing.changed && value(zeroSharing.expression.usedInputs(
                                      {0})) == std::vector<uint32_t>{0},
          "multiplication by zero keeps its syntactic read");
  auto folded =
      value(Expression::create({{base}}, {N::literal(base, "0")}, {0}));
  refuses(checkSharing(zeroed, folded, {0, 0, 0}), "ring-sharing-node");
  auto sum = value(Expression::create(
      {}, {N::literal(base, "1"), N::literal(base, "2"), N::add(0, 1)}, {2}));
  auto three = value(Expression::create({}, {N::literal(base, "3")}, {0}));
  refuses(checkSharing(sum, three, {0, 0, 0}), "ring-sharing-node");
  auto two = value(Expression::create({{base}, {extension}},
                                      {N::slot(0), N::slot(1)}, {0, 1}));
  auto permuted = value(Expression::create({{extension}, {base}},
                                           {N::slot(0), N::slot(1)}, {0, 1}));
  refuses(checkSharing(two, permuted, {0, 1}), "ring-sharing-inputs");

  // Explicit embeddings merge only when identical and keep their target field;
  // equal literals of different fields stay distinct nodes.
  auto mixed = value(Expression::create(
      {{base}, {extension}},
      {N::slot(0), N::embed(extension, 0), N::embed(extension, 0), N::slot(1),
       N::mul(1, 3), N::mul(2, 3), N::add(4, 5)},
      {6}));
  auto mixedSharing = value(shareExpression(mixed));
  require(mixedSharing.nodeMap == std::vector<uint32_t>{0, 1, 1, 2, 3, 3, 4} &&
              mixedSharing.expression.facts()[1].field == extension &&
              mixedSharing.expression.facts()[4].field == extension &&
              mixedSharing.expression.facts()[4].degree == 2,
          "identical embeddings share and keep the target field");
  agree(mixed, mixedSharing, {1, 1}, {{{5}, {7}}, {{1, 1}, {2, 3}}});
  auto literals = value(Expression::create(
      {}, {N::literal(base, "3"), N::literal(extension, "3")}, {0, 1}));
  auto literalSharing = value(shareExpression(literals));
  require(!literalSharing.changed &&
              literalSharing.expression.nodes().size() == 2,
          "equal literals of different fields are different nodes");
  agree(literals, literalSharing, {}, {{{}}});

  // Empty and constant-only arenas.
  auto empty = value(Expression::create({}, {}, {}));
  auto emptySharing = value(shareExpression(empty));
  require(!emptySharing.changed && emptySharing.nodeMap.empty() &&
              emptySharing.expression.outputs().empty(),
          "empty arena");
  agree(empty, emptySharing, {}, {{{}}});
  refuses(checkSharing(empty, three, {}), "ring-sharing-outputs");
  auto constants = value(Expression::create(
      {}, {N::literal(base, "3"), N::literal(base, "3"), N::add(0, 1)},
      {2, 0}));
  auto constantSharing = value(shareExpression(constants));
  require(constantSharing.nodeMap == std::vector<uint32_t>{0, 0, 1} &&
              constantSharing.expression.outputs() ==
                  ArrayRef<uint32_t>({1, 0}),
          "zero-input arena shares its literal");
  agree(constants, constantSharing, {}, {{{}}});

  // An arena that already shares its diamond is returned unchanged.
  auto diamond = value(Expression::create(
      {{base}, {base}}, {N::slot(0), N::slot(1), N::add(0, 1), N::mul(2, 2)},
      {3}));
  auto diamondSharing = value(shareExpression(diamond));
  require(!diamondSharing.changed &&
              diamondSharing.expression.identity() == diamond.identity(),
          "already shared arena keeps its identity");
  agree(diamond, diamondSharing, {2, 3}, {{{4}, {9}}});

  // A generated arena with exact duplicates spread across a few thousand nodes.
  uint64_t state = 7;
  auto next = [&state]() {
    state = state * 6364136223846793005ULL + 1442695040888963407ULL;
    return uint32_t(state >> 33);
  };
  std::vector<N> nodes{N::slot(0), N::slot(1), N::slot(2), N::slot(3)};
  while (nodes.size() < 3000) {
    uint32_t n = nodes.size(), pick = next() % 10;
    uint32_t a = next() % n, b = next() % n;
    if (pick < 2)
      nodes.push_back(nodes[a]);
    else if (pick == 2)
      nodes.push_back(N::literal(base, std::to_string(next() % 5)));
    else if (pick == 3)
      nodes.push_back(N::slot(next() % 4));
    else if (pick < 6)
      nodes.push_back(N::neg(a));
    else if (pick < 8)
      nodes.push_back(N::add(a, b));
    else
      nodes.push_back(N::mul(a, b));
  }
  std::vector<bool> child(nodes.size(), false);
  for (const auto &node : nodes) {
    if (node.kind == Kind::Add || node.kind == Kind::Mul)
      child[node.left] = child[node.right] = true;
    else if (node.kind == Kind::Neg)
      child[node.left] = true;
  }
  std::vector<uint32_t> roots;
  for (uint32_t i = 0; i < nodes.size(); ++i)
    if (!child[i])
      roots.push_back(i);
  require(roots.size() <= Limits::outputs,
          "generated roots fit the output limit");
  auto generated = value(Expression::create(
      {{base}, {base}, {base}, {base}}, std::move(nodes), std::move(roots)));
  auto generatedSharing = value(shareExpression(generated));
  require(generatedSharing.changed &&
              generatedSharing.expression.nodes().size() <
                  generated.nodes().size(),
          "generated duplicates merged");
  agree(generated, generatedSharing, {1, 0, 3, 2},
        {{{2}, {3}, {5}, {7}}, {{0}, {1}, {prime - 1}, {4}}});
  outs() << "ring expression sharing and its independent judgment agree with "
            "reference evaluation\n";
}
