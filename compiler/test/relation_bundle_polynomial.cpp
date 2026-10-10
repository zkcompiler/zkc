// Polynomial view of one bundle table: exact widths, authorities and
// bindings, canonical opening subjects, active scopes and the scoped quotient
// bound shared with the finite AIR analysis. The pinned recurrence fixture is
// analyzed under the two-adic profile and checked against an independent
// coefficient interpolation of its honest data; separately authored finite,
// cyclic, optional, lifted, extension and general-field tables exercise the
// remaining rules. A fixture shared with the runtime backend tests pins the
// zero-chunk encoding. Nothing here is a soundness claim about batching,
// commitments or a proof protocol.
#include "support/NativeCases.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Relation/BundlePolynomial.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include <string>
#include <vector>

using namespace llvm;
using namespace zkc::relation;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;

namespace {
const std::string KB = "koala-bear", EXT = "koala-bear.ext8-binomial3";
std::string fixtureDirectory, chunkFixture;

std::string read(StringRef name) {
  auto buffer = MemoryBuffer::getFile(fixtureDirectory + "/" + name.str());
  require(bool(buffer), "fixture " + name + " is unreadable");
  return (*buffer)->getBuffer().str();
}
Bundle bundle(StringRef text) { return take(readBundleText(text)); }
json::Value carrier(StringRef text) { return take(readBundleDataJson(text)); }
Expected<bool> accepted(Error error) {
  if (error)
    return std::move(error);
  return true;
}
AIRPolynomialParameters twoAdic(uint32_t n) {
  return take(twoAdicPolynomialParameters(n));
}
BundleScope scope(BundleScopeKind kind, uint32_t a = 0, uint32_t b = 0) {
  return {kind, a, b};
}
BundleHeight instanceHeight(uint32_t min, uint32_t max, bool pow2 = false) {
  return {BundleHeightAuthority::Instance, min, max, pow2};
}
BundleHeight fixedHeight(uint32_t h) {
  return {BundleHeightAuthority::Fixed, h, h, false};
}

/// Small arena builder: equal bindings share one ring input.
struct Arena {
  std::vector<zkc::ring::Input> inputs;
  std::vector<BundleInput> bindings;
  std::vector<zkc::ring::Node> nodes;
  std::vector<uint32_t> outputs;
  uint32_t bind(const std::string &field, BundleInput binding) {
    for (uint32_t i = 0; i < bindings.size(); ++i)
      if (bindings[i].kind == binding.kind &&
          bindings[i].index == binding.index &&
          bindings[i].offset == binding.offset &&
          bindings[i].column == binding.column) {
        nodes.push_back(zkc::ring::Node::slot(i));
        return nodes.size() - 1;
      }
    inputs.push_back({field});
    bindings.push_back(binding);
    nodes.push_back(zkc::ring::Node::slot(inputs.size() - 1));
    return nodes.size() - 1;
  }
  uint32_t read(uint32_t group, int32_t offset, uint32_t column = 0,
                const std::string &field = KB) {
    return bind(field, BundleInput::read(group, offset, column));
  }
  uint32_t pub(uint32_t slot, const std::string &field = KB) {
    return bind(field, BundleInput::publicSlot(slot));
  }
  uint32_t lit(std::string natural, const std::string &field = KB) {
    nodes.push_back(zkc::ring::Node::literal(field, std::move(natural)));
    return nodes.size() - 1;
  }
  uint32_t push(zkc::ring::Node node) {
    nodes.push_back(std::move(node));
    return nodes.size() - 1;
  }
  uint32_t add(uint32_t a, uint32_t b) {
    return push(zkc::ring::Node::add(a, b));
  }
  uint32_t mul(uint32_t a, uint32_t b) {
    return push(zkc::ring::Node::mul(a, b));
  }
  uint32_t neg(uint32_t a) { return push(zkc::ring::Node::neg(a)); }
  uint32_t sub(uint32_t a, uint32_t b) { return add(a, neg(b)); }
  uint32_t embed(const std::string &field, uint32_t a) {
    return push(zkc::ring::Node::embed(field, a));
  }
  uint32_t out(uint32_t node) {
    outputs.push_back(node);
    return outputs.size() - 1;
  }
  zkc::ring::Expression build() const {
    return take(zkc::ring::Expression::create(inputs, nodes, outputs));
  }
};
BundleTable table(std::string name, const Arena &arena,
                  std::vector<BundleGroup> groups, BundleHeight height,
                  BundleReadModel model = BundleReadModel::Finite,
                  bool optional = false) {
  return {std::move(name), optional,       height, model, std::move(groups),
          arena.build(),   arena.bindings, {},     {}};
}
Bundle single(BundleTable t, std::vector<BundleSlot> publics = {}) {
  std::vector<BundleTable> tables;
  tables.push_back(std::move(t));
  return take(Bundle::create(std::move(publics), {}, std::move(tables)));
}
/// The same bundle with its first table edited; formation is repeated.
Bundle edited(const Bundle &source, function_ref<void(BundleTable &)> edit) {
  std::vector<BundleSlot> publics(source.publics().begin(),
                                  source.publics().end());
  std::vector<BundleChannel> channels(source.channels().begin(),
                                      source.channels().end());
  std::vector<BundleTable> tables(source.tables().begin(),
                                  source.tables().end());
  edit(tables[0]);
  return take(Bundle::create(std::move(publics), std::move(channels),
                             std::move(tables)));
}
/// The complement form of every bound agrees with the scoped quotient:
/// numerator + selector - domainSize is the quotient degree when present.
void checkComplementAgreement(const BundlePolynomialView &view) {
  for (const auto &assertion : view.assertions) {
    const auto &c = assertion.bound;
    require(c.selectorDegree == view.parameters.domainSize - (c.end - c.begin),
            "selector is the complement vanishing degree");
    if (c.quotientDegree)
      require(c.numeratorDegree + c.selectorDegree -
                      view.parameters.domainSize ==
                  *c.quotientDegree,
              "complement formulation agrees with the scoped quotient");
    else
      require(c.numeratorDegree < c.end - c.begin,
              "no quotient exactly when divisibility requires zero");
  }
}
std::vector<uint64_t> quotients(const BundlePolynomialView &view) {
  std::vector<uint64_t> result;
  for (const auto &assertion : view.assertions)
    result.push_back(assertion.bound.quotientDegree
                         ? *assertion.bound.quotientDegree
                         : UINT64_MAX);
  return result;
}

/// Reference coefficient arithmetic over the fixture's prime field: dense
/// ascending coefficients with 64-bit residues. The modulus is below 2^32,
/// so every product fits before reduction. The zero polynomial is empty.
struct Reference {
  using Poly = std::vector<uint64_t>;
  uint64_t p;
  explicit Reference(StringRef modulus) : p(std::stoull(modulus.str())) {
    require(p > 2 && p < (uint64_t(1) << 32), "reference modulus width");
  }
  uint64_t add(uint64_t a, uint64_t b) const { return (a + b) % p; }
  uint64_t sub(uint64_t a, uint64_t b) const { return (a + p - b) % p; }
  uint64_t mul(uint64_t a, uint64_t b) const { return a * b % p; }
  uint64_t pow(uint64_t a, uint64_t e) const {
    uint64_t r = 1;
    for (a %= p; e; e >>= 1, a = mul(a, a))
      if (e & 1)
        r = mul(r, a);
    return r;
  }
  uint64_t inv(uint64_t a) const {
    require(a % p, "inverse of zero");
    return pow(a, p - 2);
  }
  uint64_t parse(StringRef text) const {
    uint64_t value = std::stoull(text.str());
    require(value < p, "canonical residue");
    return value;
  }
  static Poly trim(Poly a) {
    while (!a.empty() && !a.back())
      a.pop_back();
    return a;
  }
  static int64_t degree(const Poly &a) { return int64_t(trim(a).size()) - 1; }
  Poly addP(Poly a, const Poly &b) const {
    if (a.size() < b.size())
      a.resize(b.size(), 0);
    for (size_t i = 0; i < b.size(); ++i)
      a[i] = add(a[i], b[i]);
    return trim(a);
  }
  Poly negP(Poly a) const {
    for (auto &c : a)
      c = c ? p - c : 0;
    return a;
  }
  Poly mulP(const Poly &a, const Poly &b) const {
    if (a.empty() || b.empty())
      return {};
    Poly r(a.size() + b.size() - 1, 0);
    for (size_t i = 0; i < a.size(); ++i)
      for (size_t j = 0; j < b.size(); ++j)
        r[i + j] = add(r[i + j], mul(a[i], b[j]));
    return trim(r);
  }
  /// T(s X): coefficient j scaled by s^j.
  Poly shift(Poly a, uint64_t s) const {
    uint64_t power = 1;
    for (auto &c : a) {
      c = mul(c, power);
      power = mul(power, s);
    }
    return trim(a);
  }
  uint64_t eval(const Poly &a, uint64_t x) const {
    uint64_t r = 0;
    for (auto it = a.rbegin(); it != a.rend(); ++it)
      r = add(mul(r, x), *it);
    return r;
  }
  /// Long division by a nonzero divisor: (quotient, remainder).
  std::pair<Poly, Poly> divide(Poly a, const Poly &d) const {
    Poly divisor = trim(d);
    require(!divisor.empty(), "division by zero");
    a = trim(a);
    if (a.size() < divisor.size())
      return {{}, a};
    Poly q(a.size() - divisor.size() + 1, 0);
    const uint64_t lead = inv(divisor.back());
    for (size_t k = q.size(); k-- > 0;) {
      const uint64_t c = mul(a[k + divisor.size() - 1], lead);
      q[k] = c;
      for (size_t j = 0; j < divisor.size(); ++j)
        a[k + j] = sub(a[k + j], mul(c, divisor[j]));
    }
    return {trim(q), trim(a)};
  }
  Poly vanishing(ArrayRef<uint64_t> points) const {
    Poly z{1};
    for (auto x : points)
      z = mulP(z, {sub(0, x), 1});
    return z;
  }
  Poly interpolate(ArrayRef<uint64_t> xs, ArrayRef<uint64_t> ys) const {
    Poly result;
    for (size_t i = 0; i < xs.size(); ++i) {
      Poly basis{1};
      uint64_t denominator = 1;
      for (size_t j = 0; j < xs.size(); ++j) {
        if (j == i)
          continue;
        basis = mulP(basis, {sub(0, xs[j]), 1});
        denominator = mul(denominator, sub(xs[i], xs[j]));
      }
      const uint64_t scale = mul(ys[i], inv(denominator));
      for (auto &c : basis)
        c = mul(c, scale);
      result = addP(result, basis);
    }
    return result;
  }
};
/// Interprets the arena over coefficient polynomials with the bound inputs.
struct PolynomialAlgebra {
  const Reference &f;
  const std::vector<Reference::Poly> &inputs;
  Expected<Reference::Poly> input(uint32_t index, StringRef) {
    return inputs[index];
  }
  Expected<Reference::Poly> constant(StringRef, StringRef natural) {
    return Reference::trim({f.parse(natural)});
  }
  Expected<Reference::Poly> add(StringRef, const Reference::Poly &a,
                                const Reference::Poly &b) {
    return f.addP(a, b);
  }
  Expected<Reference::Poly> mul(StringRef, const Reference::Poly &a,
                                const Reference::Poly &b) {
    return f.mulP(a, b);
  }
  Expected<Reference::Poly> neg(StringRef, const Reference::Poly &a) {
    return f.negP(a);
  }
  Expected<Reference::Poly> embed(StringRef, StringRef,
                                  const Reference::Poly &) {
    return zkc::error("reference-embedding");
  }
};
} // namespace

int main(int argc, char **argv) {
  require(argc == 3, "usage: relation_bundle_polynomial FIXTURE_DIRECTORY "
                     "CHUNK_FIXTURE");
  fixtureDirectory = argv[1];
  chunkFixture = argv[2];
  zkc::test::Cases cases;

  cases.run("two-adic profile parameters", [] {
    auto n8 = twoAdic(8);
    require(n8.height == 8 && n8.domainSize == 8 && n8.traceDegree == 7,
            "height = domainSize = n and traceDegree = n - 1");
    require(twoAdic(2).traceDegree == 1, "smallest profile height");
    for (uint32_t n : {0u, 1u, 6u, 12u, AIRPolynomialParameters::sizeLimit * 2})
      refuses(twoAdicPolynomialParameters(n), "bundle-polynomial-two-adic");
  });

  cases.run("recurrence fixture under the two-adic profile", [] {
    auto recurrence = bundle(read("bundle.json"));
    auto view = take(analyzeBundlePolynomials(recurrence, 0, KB, twoAdic(8)));
    require(view.relation == recurrence.identity() && view.table == 0 &&
                view.name == "main" && view.field == KB &&
                view.coordinates == 1 && !view.optional &&
                view.readModel == BundleReadModel::Cyclic &&
                view.heightPolicy.authority == BundleHeightAuthority::Fixed &&
                view.heightPolicy.min == 8 &&
                view.profile == BundlePolynomialProfile::TwoAdicNatural,
            "recurrence table facts and profile");
    require(view.groups.size() == 2 && view.groups[0].name == "main" &&
                view.groups[0].authority == BundleAuthority::Witness &&
                view.groups[0].width == 4 &&
                view.groups[0].offsets == std::vector<int32_t>{0, 1} &&
                view.groups[1].name == "preprocessed" &&
                view.groups[1].authority == BundleAuthority::Config &&
                view.groups[1].width == 1 &&
                view.groups[1].offsets == std::vector<int32_t>{0},
            "exact group widths, authorities and distinct offsets");
    const auto &inputs = recurrence.tables()[0].inputs;
    require(view.bindings.size() == 11 &&
                std::equal(view.bindings.begin(), view.bindings.end(),
                           inputs.begin(), inputs.end(),
                           [](const BundleInput &a, const BundleInput &b) {
                             return a.kind == b.kind && a.index == b.index &&
                                    a.offset == b.offset &&
                                    a.column == b.column;
                           }),
            "ordered bindings are the arena inputs");
    require(view.publics == std::vector<uint32_t>{0, 1, 2},
            "every public slot is bound by an active assertion");
    require(view.reads == std::vector<BundleRead>{{0, 0, 0},
                                                  {0, 0, 1},
                                                  {0, 0, 2},
                                                  {0, 0, 3},
                                                  {0, 1, 0},
                                                  {0, 1, 1},
                                                  {0, 1, 3},
                                                  {1, 0, 0}},
            "canonical distinct opening subjects");
    require(view.assertions.size() == 9 && view.activeAssertions == 9,
            "every fixture assertion is active at height 8");
    const uint32_t degrees[] = {2, 1, 1, 1, 1, 1, 3, 1, 1};
    const uint32_t begins[] = {0, 0, 0, 0, 0, 0, 0, 7, 7};
    const uint32_t ends[] = {8, 1, 1, 1, 7, 7, 7, 8, 8};
    const uint32_t selectors[] = {0, 7, 7, 7, 1, 1, 1, 7, 7};
    const uint64_t expected[] = {6, 6, 6, 6, 0, 0, 14, 6, 6};
    for (unsigned i = 0; i < 9; ++i) {
      const auto &a = view.assertions[i];
      require(a.output == recurrence.tables()[0].assertions[i].output &&
                  a.degree == degrees[i] && a.bound.begin == begins[i] &&
                  a.bound.end == ends[i] &&
                  a.bound.selectorDegree == selectors[i] &&
                  a.bound.numeratorDegree == uint64_t(degrees[i]) * 7 &&
                  a.bound.quotientDegree == expected[i],
              "fixture assertion " + Twine(i) + " bound");
    }
    checkComplementAgreement(view);
    require(view.maxQuotientDegree == 14 && view.quotientChunks == 2,
            "maximum quotient degree 14 needs two coefficient blocks");
    // A public slot contributes degree zero while every read, including the
    // configuration column, contributes one: assertion 1 reads one witness
    // column against a public slot; assertion 6 multiplies two witness reads
    // by the configuration read.
    require(view.assertions[1].degree == 1 && view.assertions[6].degree == 3,
            "public degree zero versus read degree one");
    require(view.arena == recurrence.tables()[0].arena.identity(),
            "arena identity names the table arena");
    require(take(bundlePolynomialArena(recurrence, view)) ==
                &recurrence.tables()[0].arena,
            "the arena stays borrowed from the admitted bundle");
    auto encoded = zkc::printJson(view.encode());
    require(encoded == zkc::printJson(view.encode()), "deterministic encoding");
    require(encoded.find("\"zkc.relation-bundle-polynomial-analysis/0\"") !=
                    std::string::npos &&
                encoded.find("\"two-adic-natural\"") != std::string::npos &&
                encoded.find("\"quotient_chunks\":2") != std::string::npos,
            "encoding names its schema, profile and chunk count");
  });

  cases.run("recurrence refusals and general parameters", [] {
    auto recurrence = bundle(read("bundle.json"));
    refuses(analyzeBundlePolynomials(recurrence, 1, KB, twoAdic(8)),
            "relation-table-index");
    refuses(analyzeBundlePolynomials(recurrence, 0, "bls12-381.fr", twoAdic(8)),
            "relation-table-carrier");
    refuses(analyzeBundlePolynomials(recurrence, 0, KB, {7, 7, 6}),
            "bundle-height");
    refuses(analyzeBundlePolynomials(recurrence, 0, KB, twoAdic(16)),
            "bundle-height");
    refuses(analyzeBundlePolynomials(recurrence, 0, KB, {0, 8, 7}),
            "air-polynomial-height");
    refuses(
        analyzeBundlePolynomials(
            recurrence, 0, KB, {AIRPolynomialParameters::sizeLimit + 1, 8, 7}),
        "air-polynomial-height");
    refuses(analyzeBundlePolynomials(recurrence, 0, KB, {8, 4, 7}),
            "air-polynomial-domain-size");
    refuses(
        analyzeBundlePolynomials(
            recurrence, 0, KB, {8, AIRPolynomialParameters::sizeLimit + 1, 7}),
        "air-polynomial-domain-size");
    refuses(analyzeBundlePolynomials(recurrence, 0, KB, {8, 8, 6}),
            "air-polynomial-trace-degree");
    refuses(
        analyzeBundlePolynomials(
            recurrence, 0, KB, {8, 8, AIRPolynomialParameters::sizeLimit + 1}),
        "air-polynomial-trace-degree");
    // A cyclic read wraps in the height domain; padding it has no meaning.
    refuses(analyzeBundlePolynomials(recurrence, 0, KB, {8, 16, 15}),
            "bundle-polynomial-domain");
    // Masking beyond n - 1 keeps the wrap law but leaves the profile.
    auto masked = take(analyzeBundlePolynomials(recurrence, 0, KB, {8, 8, 8}));
    require(masked.profile == BundlePolynomialProfile::General &&
                masked.maxQuotientDegree == 17 && masked.quotientChunks == 3 &&
                quotients(masked) ==
                    std::vector<uint64_t>{8, 7, 7, 7, 1, 1, 17, 7, 7},
            "general trace degree raises every bound");
    checkComplementAgreement(masked);
  });

  cases.run("edited assertions, reads and authorities change the subject", [] {
    auto recurrence = bundle(read("bundle.json"));
    auto view = take(analyzeBundlePolynomials(recurrence, 0, KB, twoAdic(8)));
    auto widened = edited(recurrence, [](BundleTable &t) {
      t.assertions[6].scope = scope(BundleScopeKind::All);
    });
    auto widenedView =
        take(analyzeBundlePolynomials(widened, 0, KB, twoAdic(8)));
    require(widenedView.assertions[6].bound.quotientDegree == 13 &&
                widenedView.assertions[6].bound.selectorDegree == 0 &&
                widenedView.quotientChunks == 2,
            "a wider scope lowers the quotient bound");
    auto narrowed = edited(recurrence, [](BundleTable &t) {
      t.assertions[6].scope = scope(BundleScopeKind::First);
    });
    auto narrowedView =
        take(analyzeBundlePolynomials(narrowed, 0, KB, twoAdic(8)));
    require(narrowedView.assertions[6].bound.quotientDegree == 20 &&
                narrowedView.maxQuotientDegree == 20 &&
                narrowedView.quotientChunks == 3,
            "a narrower scope raises the bound and the chunk count");
    auto reversed = edited(recurrence, [](BundleTable &t) {
      require(t.inputs[6].kind == BundleInput::Kind::Read &&
                  t.inputs[6].offset == 1,
              "fixture input 6 is the next-row read of column 3");
      t.inputs[6].offset = -1;
    });
    auto reversedView =
        take(analyzeBundlePolynomials(reversed, 0, KB, twoAdic(8)));
    require(reversedView.groups[0].offsets == std::vector<int32_t>{-1, 0, 1} &&
                reversedView.reads[0] == BundleRead{0, -1, 3} &&
                reversedView.reads.size() == 8,
            "a negative offset is preserved as a distinct subject");
    require(zkc::printJson(reversedView.encode()) !=
                    zkc::printJson(view.encode()) &&
                zkc::printJson(reversedView.encode()).find("[0,\"-1\",3]") !=
                    std::string::npos,
            "the encoding names the signed shift");
    auto disclosed = edited(recurrence, [](BundleTable &t) {
      t.groups[0].authority = BundleAuthority::Public;
    });
    auto disclosedView =
        take(analyzeBundlePolynomials(disclosed, 0, KB, twoAdic(8)));
    require(disclosedView.groups[0].authority == BundleAuthority::Public &&
                disclosedView.assertions[6].degree == 3 &&
                quotients(disclosedView) == quotients(view),
            "authority changes the described group, never a read's degree");
    refuses(bundlePolynomialArena(widened, view), "bundle-polynomial-relation");
    auto moved = view;
    moved.table = 1;
    refuses(bundlePolynomialArena(recurrence, moved),
            "bundle-polynomial-relation");
    auto renamed = view;
    renamed.arena = std::string(64, '0');
    refuses(bundlePolynomialArena(recurrence, renamed),
            "bundle-polynomial-relation");
  });

  cases.run("finite scopes, padding and windows", [] {
    // interior(0,1): x0' - x0; first: x0 - p; all: x0 * x1; interval(0,2):
    // x0'; last: x1 - x1(-1); interval(2,2): x0(-2); all: x1 - p; first:
    // p * p.
    Arena a;
    a.out(a.sub(a.read(0, 1, 0), a.read(0, 0, 0)));
    a.out(a.sub(a.read(0, 0, 0), a.pub(0)));
    a.out(a.mul(a.read(0, 0, 0), a.read(0, 0, 1)));
    a.out(a.read(0, 1, 0));
    a.out(a.sub(a.read(0, 0, 1), a.read(0, -1, 1)));
    a.out(a.read(0, -2, 0));
    a.out(a.sub(a.read(0, 0, 1), a.pub(0)));
    a.out(a.mul(a.pub(0), a.pub(0)));
    auto t = table("t", a, {{"w", BundleAuthority::Witness, KB, 2}},
                   instanceHeight(1, 16));
    t.assertions = {{0, scope(BundleScopeKind::Interior, 0, 1)},
                    {1, scope(BundleScopeKind::First)},
                    {2, scope(BundleScopeKind::All)},
                    {3, scope(BundleScopeKind::Interval, 0, 2)},
                    {4, scope(BundleScopeKind::Last)},
                    {5, scope(BundleScopeKind::Interval, 2, 2)},
                    {6, scope(BundleScopeKind::All)},
                    {7, scope(BundleScopeKind::First)}};
    auto b = single(std::move(t), {{"p", KB}});
    auto view = take(analyzeBundlePolynomials(b, 0, KB, twoAdic(8)));
    require(view.readModel == BundleReadModel::Finite &&
                view.profile == BundlePolynomialProfile::TwoAdicNatural &&
                view.activeAssertions == 7 &&
                !view.assertions[5].bound.active(),
            "a finite power-of-two height fits the profile; interval(2,2) is "
            "empty");
    require(view.groups[0].offsets == std::vector<int32_t>{-1, 0, 1} &&
                view.reads ==
                    std::vector<BundleRead>{
                        {0, -1, 1}, {0, 0, 0}, {0, 0, 1}, {0, 1, 0}} &&
                view.publics == std::vector<uint32_t>{0},
            "the inactive assertion's read at offset -2 is not a subject");
    const uint32_t begins[] = {0, 0, 0, 0, 7, 2, 0, 0};
    const uint32_t ends[] = {7, 1, 8, 2, 8, 2, 8, 1};
    for (unsigned i = 0; i < 8; ++i)
      require(view.assertions[i].bound.begin == begins[i] &&
                  view.assertions[i].bound.end == ends[i],
              "finite active rows of assertion " + Twine(i));
    // The inactive interval keeps the vacuous numerator - 0 bound, which
    // imposes nothing.
    require(quotients(view) ==
                std::vector<uint64_t>{0, 6, 6, 5, 6, 7, UINT64_MAX, UINT64_MAX},
            "scoped quotient bounds at height 8");
    // A degree-one numerator of degree 7 on all eight rows and a public-only
    // numerator on the first row can only be divisible when zero; they keep
    // their reads and impose no chunk.
    require(view.assertions[6].bound.active() &&
                !view.assertions[6].bound.quotientDegree &&
                view.assertions[7].degree == 0 &&
                !view.assertions[7].bound.quotientDegree &&
                view.maxQuotientDegree == 6 && view.quotientChunks == 1,
            "divisibility requiring zero has no quotient");
    checkComplementAgreement(view);
    // Padding a height-5 table into the size-8 domain keeps the original
    // active rows and leaves the profile.
    auto padded = take(analyzeBundlePolynomials(b, 0, KB, {5, 8, 7}));
    require(padded.profile == BundlePolynomialProfile::General &&
                padded.assertions[2].bound.end == 5 &&
                padded.assertions[2].bound.selectorDegree == 3 &&
                padded.assertions[4].bound.begin == 4 &&
                padded.assertions[0].bound.end == 4 &&
                padded.assertions[2].bound.quotientDegree == 9 &&
                padded.quotientChunks == 2,
            "padding never adds active rows");
    checkComplementAgreement(padded);
    // The next-row read of interval [0,2) has no row 2 at height 2, and the
    // interval itself does not fit at height 1.
    refuses(analyzeBundlePolynomials(b, 0, KB, {2, 2, 1}), "bundle-window");
    refuses(analyzeBundlePolynomials(b, 0, KB, {1, 1, 0}),
            "bundle-scope-height");
    refuses(analyzeBundlePolynomials(b, 0, KB, {17, 32, 31}), "bundle-height");
    // A finite table never wraps: an all-rows read at offset 1 refuses at
    // formation, before any polynomial view exists.
    Arena wrapping;
    wrapping.out(wrapping.read(0, 1, 0));
    auto w = table("w", wrapping, {{"w", BundleAuthority::Witness, KB, 1}},
                   instanceHeight(1, 8));
    w.assertions = {{0, scope(BundleScopeKind::All)}};
    std::vector<BundleTable> tables{std::move(w)};
    refuses(Bundle::create({}, {}, std::move(tables)), "bundle-window");
  });

  cases.run("analysis work is independent of the height", [] {
    Arena a;
    a.out(a.mul(a.read(0, 0, 0), a.mul(a.read(0, 1, 0), a.read(0, 2, 0))));
    auto t = table("t", a, {{"w", BundleAuthority::Witness, KB, 1}},
                   instanceHeight(1, BundleLimits::height));
    t.assertions = {{0, scope(BundleScopeKind::Interior, 0, 2)}};
    auto b = single(std::move(t));
    const uint32_t n = BundleLimits::height;
    auto view = take(analyzeBundlePolynomials(b, 0, KB, twoAdic(n)));
    require(view.assertions[0].bound.end == n - 2 &&
                view.assertions[0].bound.quotientDegree ==
                    uint64_t(3) * (n - 1) - (n - 2) &&
                view.quotientChunks == 2,
            "bounds at the largest bundle height");
    auto inactive = take(analyzeBundlePolynomials(b, 0, KB, twoAdic(2)));
    require(!inactive.assertions[0].bound.active() && inactive.reads.empty() &&
                !inactive.quotientChunks && !inactive.maxQuotientDegree,
            "an empty interior scope has no quotient or opening subject");
  });

  cases.run("public, witness and configuration degrees", [] {
    // first: p * x; first: x * x; first: c * x; first: p * p * x, where the
    // last two assertions share one output under different scopes.
    Arena a;
    a.out(a.mul(a.pub(0), a.read(1, 0, 0)));
    a.out(a.mul(a.read(1, 0, 0), a.read(1, 0, 0)));
    a.out(a.mul(a.read(0, 0, 0), a.read(1, 0, 0)));
    a.out(a.mul(a.mul(a.pub(0), a.pub(0)), a.read(1, 0, 0)));
    auto t = table("t", a,
                   {{"c", BundleAuthority::Config, KB, 1},
                    {"x", BundleAuthority::Witness, KB, 1}},
                   fixedHeight(8));
    t.assertions = {{0, scope(BundleScopeKind::First)},
                    {1, scope(BundleScopeKind::First)},
                    {2, scope(BundleScopeKind::First)},
                    {3, scope(BundleScopeKind::First)},
                    {3, scope(BundleScopeKind::Last)}};
    auto b = single(std::move(t), {{"p", KB}});
    auto view = take(analyzeBundlePolynomials(b, 0, KB, twoAdic(8)));
    require(view.assertions[0].degree == 1 && view.assertions[1].degree == 2 &&
                view.assertions[2].degree == 2 &&
                view.assertions[3].degree == 1,
            "public slots weigh zero; witness and configuration reads one");
    require(quotients(view) == std::vector<uint64_t>{6, 13, 13, 6, 6} &&
                view.activeAssertions == 5 &&
                view.reads == std::vector<BundleRead>{{0, 0, 0}, {1, 0, 0}} &&
                view.groups[0].offsets == std::vector<int32_t>{0} &&
                view.groups[1].offsets == std::vector<int32_t>{0},
            "shared outputs do not duplicate subjects");
  });

  cases.run("cyclic tables need the exact two-adic height domain", [] {
    auto cyclic = [](uint32_t height, bool fixed = true) {
      // all: x - k * x'; interior(1,0): x - q(-1)[1].
      Arena a;
      a.out(a.sub(a.read(1, 0, 0), a.mul(a.read(0, 0, 0), a.read(1, 1, 0))));
      a.out(a.sub(a.read(1, 0, 0), a.read(2, -1, 1)));
      auto t = table(
          "c", a,
          {{"k", BundleAuthority::Config, KB, 1},
           {"x", BundleAuthority::Witness, KB, 1},
           {"q", BundleAuthority::Public, KB, 2}},
          fixed ? fixedHeight(height)
                : BundleHeight{BundleHeightAuthority::Config, 2, height, true},
          BundleReadModel::Cyclic);
      t.assertions = {{0, scope(BundleScopeKind::All)},
                      {1, scope(BundleScopeKind::Interior, 1, 0)}};
      return single(std::move(t));
    };
    auto four = cyclic(4);
    auto view = take(analyzeBundlePolynomials(four, 0, KB, twoAdic(4)));
    require(view.profile == BundlePolynomialProfile::TwoAdicNatural &&
                view.groups[0].offsets == std::vector<int32_t>{0} &&
                view.groups[1].offsets == std::vector<int32_t>{0, 1} &&
                view.groups[2].offsets == std::vector<int32_t>{-1} &&
                view.groups[2].authority == BundleAuthority::Public &&
                quotients(view) == std::vector<uint64_t>{2, 0},
            "wrapping next-row and previous-row reads are subjects");
    checkComplementAgreement(view);
    refuses(analyzeBundlePolynomials(four, 0, KB, {4, 8, 7}),
            "bundle-polynomial-domain");
    refuses(analyzeBundlePolynomials(cyclic(6), 0, KB, {6, 6, 5}),
            "bundle-polynomial-domain");
    refuses(analyzeBundlePolynomials(cyclic(3), 0, KB, {3, 3, 2}),
            "bundle-polynomial-domain");
    auto configured = cyclic(8, false);
    require(take(analyzeBundlePolynomials(configured, 0, KB, twoAdic(8)))
                    .quotientChunks == 1,
            "configured power-of-two heights are admitted");
    refuses(analyzeBundlePolynomials(configured, 0, KB, twoAdic(16)),
            "bundle-height");
  });

  cases.run("optional and extension tables", [] {
    Arena a;
    a.out(a.read(0, 0, 0));
    auto t = table("o", a, {{"w", BundleAuthority::Witness, KB, 1}},
                   instanceHeight(1, 4, true), BundleReadModel::Finite, true);
    t.assertions = {{0, scope(BundleScopeKind::All)}};
    auto optional = single(std::move(t));
    auto view = take(analyzeBundlePolynomials(optional, 0, KB, twoAdic(4)));
    // The view describes the table when present; presence is the instance's.
    require(view.optional && view.heightPolicy.powerOfTwo &&
                view.activeAssertions == 1 &&
                !view.assertions[0].bound.quotientDegree,
            "an optional table is viewed conditionally");
    refuses(analyzeBundlePolynomials(optional, 0, KB, {3, 4, 3}),
            "bundle-height");
    Arena e;
    e.out(e.sub(e.read(0, 0, 0, EXT), e.embed(EXT, e.lit("3"))));
    auto x = table("e", e, {{"w", BundleAuthority::Witness, EXT, 1}},
                   fixedHeight(2));
    x.assertions = {{0, scope(BundleScopeKind::All)}};
    auto extension = single(std::move(x));
    auto extended =
        take(analyzeBundlePolynomials(extension, 0, EXT, twoAdic(2)));
    require(extended.coordinates == 8 &&
                extended.profile == BundlePolynomialProfile::TwoAdicNatural &&
                extended.assertions[0].degree == 1 &&
                !extended.assertions[0].bound.quotientDegree,
            "an extension carrier keeps its prime subfield's two-adic domain");
    refuses(analyzeBundlePolynomials(extension, 0, KB, twoAdic(2)),
            "relation-table-carrier");
  });

  cases.run("an extension carrier lifts base tables; rows stay exact", [] {
    auto recurrence = bundle(read("bundle.json"));
    auto base = take(analyzeBundlePolynomials(recurrence, 0, KB, twoAdic(8)));
    auto lifted =
        take(analyzeBundlePolynomials(recurrence, 0, EXT, twoAdic(8)));
    require(lifted.field == EXT && lifted.coordinates == 8 &&
                lifted.profile == BundlePolynomialProfile::TwoAdicNatural &&
                lifted.groups[0].field == KB && lifted.groups[1].field == KB,
            "a KoalaBear table is interpreted with every Ext8 coordinate");
    require(quotients(lifted) == quotients(base) &&
                lifted.reads == base.reads && lifted.publics == base.publics &&
                lifted.quotientChunks == base.quotientChunks &&
                lifted.arena == base.arena,
            "lifting changes no degree, subject or arena");
    require(zkc::printJson(lifted.encode()).find("\"coordinates\":8") !=
                std::string::npos,
            "the encoding records the carrier's coordinates");
    // The actual-row evaluator and the polynomial kernels keep their own
    // static rules over one admission.
    refuses(bundleTableView(recurrence, 0, EXT), "relation-table-carrier");
    take(bundleTableView(recurrence, 0, KB));
    take(accepted(checkBundlePolynomialTable(recurrence, 0, EXT)));
    // Base nodes embedded into an Ext8 output need the extension carrier;
    // an Ext8 public slot is never narrowed either.
    Arena e;
    e.out(e.embed(EXT, e.mul(e.read(0, 0, 0), e.read(0, 0, 0))));
    auto x =
        table("e", e, {{"w", BundleAuthority::Witness, KB, 1}}, fixedHeight(4));
    x.assertions = {{0, scope(BundleScopeKind::All)}};
    auto embedded = single(std::move(x));
    require(take(analyzeBundlePolynomials(embedded, 0, EXT, twoAdic(4)))
                    .assertions[0]
                    .degree == 2,
            "an embedded base product keeps its degree");
    refuses(analyzeBundlePolynomials(embedded, 0, KB, twoAdic(4)),
            "relation-table-carrier");
    refuses(bundleTableView(embedded, 0, KB), "relation-table-carrier");
    Arena s;
    s.out(s.sub(s.embed(EXT, s.read(0, 0, 0)), s.pub(0, EXT)));
    auto y =
        table("s", s, {{"w", BundleAuthority::Witness, KB, 1}}, fixedHeight(4));
    y.assertions = {{0, scope(BundleScopeKind::First)}};
    auto slot = single(std::move(y), {{"p", EXT}});
    refuses(analyzeBundlePolynomials(slot, 0, KB, twoAdic(4)),
            "relation-table-carrier");
  });

  cases.run("general fields and parameters keep the general profile", [] {
    // x * x' on interior(0, 1) over a prime field without and with the
    // installed two-adic capability.
    auto quadratic = [](const std::string &field, BundleReadModel model) {
      Arena a;
      a.out(a.mul(a.read(0, 0, 0, field), a.read(0, 1, 0, field)));
      auto t = table("q", a, {{"w", BundleAuthority::Witness, field, 1}},
                     instanceHeight(2, 64), model);
      t.assertions = {{0, scope(BundleScopeKind::Interior, 0, 1)}};
      return single(std::move(t));
    };
    const std::string BLS = "bls12-381.fr", BN = "bn254.fr";
    auto finite = quadratic(BLS, BundleReadModel::Finite);
    auto padded = take(analyzeBundlePolynomials(finite, 0, BLS, {5, 8, 7}));
    require(padded.profile == BundlePolynomialProfile::General &&
                padded.coordinates == 1 &&
                quotients(padded) == std::vector<uint64_t>{10},
            "a finite table over any presented prime field is analyzed");
    require(
        take(analyzeBundlePolynomials(finite, 0, BLS, twoAdic(8))).profile ==
            BundlePolynomialProfile::General,
        "without a two-adic root the natural parameters are general");
    refuses(analyzeBundlePolynomials(quadratic(BLS, BundleReadModel::Cyclic), 0,
                                     BLS, twoAdic(8)),
            "bundle-polynomial-domain");
    refuses(accepted(checkBundlePolynomialTable(finite, 0, BLS)),
            "bundle-polynomial-two-adic");
    // The kernels' profile is a capability rule; only KoalaBear and Ext8
    // providers implement them.
    auto cyclic = quadratic(BN, BundleReadModel::Cyclic);
    require(take(analyzeBundlePolynomials(cyclic, 0, BN, twoAdic(8))).profile ==
                BundlePolynomialProfile::TwoAdicNatural,
            "a two-adic prime field has the natural profile");
    take(accepted(checkBundlePolynomialTable(cyclic, 0, BN)));
    refuses(analyzeBundlePolynomials(cyclic, 0, KB, twoAdic(8)),
            "relation-table-carrier");
  });

  cases.run("quotient chunk encoding against the runtime shape", [] {
    // The analysis encodes "no active quotient" as zero chunks. The runtime
    // backend test reads this same fixture and expects
    // relation.table_shape at height n to report max(1, chunks).
    auto buffer = MemoryBuffer::getFile(chunkFixture);
    require(bool(buffer), "chunk fixture is unreadable");
    auto fixture = take(json::parse((*buffer)->getBuffer()));
    unsigned checked = 0, zeros = 0;
    for (const auto &entry : *fixture.getAsArray()) {
      const auto &object = *entry.getAsObject();
      const std::string name = object.getString("name")->str();
      auto b = bundle(zkc::printJson(*object.get("bundle")));
      for (const auto &pair : *object.getArray("chunks")) {
        const auto &row = *pair.getAsArray();
        const auto n = uint32_t(*row[0].getAsUINT64());
        const auto expected = *row[1].getAsUINT64();
        for (StringRef field : {StringRef(KB), StringRef(EXT)}) {
          auto view = take(analyzeBundlePolynomials(b, 0, field, twoAdic(n)));
          require(view.profile == BundlePolynomialProfile::TwoAdicNatural &&
                      view.quotientChunks == expected,
                  name + " at height " + Twine(n));
          checkComplementAgreement(view);
        }
        ++checked;
        zeros += expected == 0;
      }
    }
    require(checked == 14 && zeros == 7,
            "the fixture covers the zero encoding");
  });

  cases.run("coefficient divisibility of the honest recurrence data", [] {
    auto recurrence = bundle(read("bundle.json"));
    auto view = take(analyzeBundlePolynomials(recurrence, 0, KB, twoAdic(8)));
    auto tableView = take(bundleTableView(recurrence, 0, KB));
    auto config = take(readBundleConfiguration(
        recurrence, carrier(read("bundle-configuration.json"))));
    auto instance = take(
        readBundleInstance(recurrence, carrier(read("bundle-instance.json"))));
    auto witness = take(
        readBundleWitness(recurrence, carrier(read("bundle-witness.json"))));
    auto data = take(
        sliceBundleTableData(recurrence, tableView, config, instance, witness));
    const Reference f(zkc::protocol::fieldModulus(KB));
    const uint32_t n = view.parameters.height;
    // The installed two-adic root of order n in natural row order.
    const uint64_t g = f.pow(1791270792, (uint64_t(1) << 24) / n);
    require(f.pow(g, n) == 1 && f.pow(g, n / 2) != 1, "root of exact order n");
    std::vector<uint64_t> points;
    for (uint32_t i = 0; i < n; ++i)
      points.push_back(f.pow(g, i));
    // Column interpolants per group from the kernel layout: groups of one
    // authority are concatenated in declaration order, each row-major.
    auto interpolants = [&](const BundleColumns &witnessData) {
      std::vector<std::vector<Reference::Poly>> columns(view.groups.size());
      uint32_t start[3] = {0, 0, 0};
      for (size_t gi = 0; gi < view.groups.size(); ++gi) {
        const auto &group = view.groups[gi];
        const unsigned authority =
            group.authority == BundleAuthority::Witness  ? 0
            : group.authority == BundleAuthority::Config ? 1
                                                         : 2;
        const BundleColumns &values = authority == 0   ? witnessData
                                      : authority == 1 ? data.configuration
                                                       : data.publicData;
        const uint32_t base =
            (authority == 2 ? tableView.publicSlots : 0) + start[authority] * n;
        for (uint32_t c = 0; c < group.width; ++c) {
          std::vector<uint64_t> ys;
          for (uint32_t r = 0; r < n; ++r)
            ys.push_back(f.parse(values[base + r * group.width + c]));
          columns[gi].push_back(f.interpolate(points, ys));
        }
        start[authority] += group.width;
      }
      return columns;
    };
    auto inputsFor = [&](const BundleColumns &witnessData) {
      auto columns = interpolants(witnessData);
      std::vector<Reference::Poly> inputs;
      for (const auto &binding : view.bindings) {
        if (binding.kind == BundleInput::Kind::Public) {
          inputs.push_back(
              Reference::trim({f.parse(data.publicData[binding.index])}));
          continue;
        }
        // A read at signed offset k is T(g^k X); on a cyclic table the
        // exponent wraps modulo n.
        const uint64_t exponent =
            uint64_t((binding.offset % int64_t(n) + int64_t(n)) % int64_t(n));
        inputs.push_back(f.shift(columns[binding.index][binding.column],
                                 f.pow(g, exponent)));
      }
      return inputs;
    };
    const auto *arena = take(bundlePolynomialArena(recurrence, view));
    std::vector<uint32_t> positions;
    for (const auto &assertion : view.assertions)
      positions.push_back(assertion.output);
    auto numerators = [&](const BundleColumns &witnessData) {
      auto inputs = inputsFor(witnessData);
      PolynomialAlgebra algebra{f, inputs};
      return take(arena->evaluate<Reference::Poly>(positions, algebra));
    };
    const auto honest = numerators(data.witness);
    const auto zh = f.vanishing(points);
    int64_t largest = -1;
    std::vector<Reference::Poly> quotientPolys;
    for (size_t i = 0; i < view.assertions.size(); ++i) {
      const auto &bound = view.assertions[i].bound;
      const auto &c = honest[i];
      require(Reference::degree(c) <= int64_t(bound.numeratorDegree),
              "numerator within the read-degree bound");
      std::vector<uint64_t> rows(points.begin() + bound.begin,
                                 points.begin() + bound.end);
      const auto zs = f.vanishing(rows);
      auto [q, r] = f.divide(c, zs);
      require(r.empty(), "honest numerator " + Twine(i) + " divisible by Z_S");
      if (bound.quotientDegree)
        require(Reference::degree(q) <= int64_t(*bound.quotientDegree),
                "quotient within the scoped bound");
      else
        require(q.empty(), "zero when divisibility requires zero");
      const uint64_t blocks = q.empty() ? 0 : (q.size() + n - 1) / n;
      require(blocks <= view.quotientChunks, "chunk count holds the quotient");
      // Complement form: Z_H divides C * (Z_H / Z_S) with the same quotient.
      auto [s, sr] = f.divide(zh, zs);
      require(sr.empty() &&
                  Reference::degree(s) == int64_t(bound.selectorDegree),
              "the selector is the complement vanishing polynomial");
      auto [q2, r2] = f.divide(f.mulP(c, s), zh);
      require(r2.empty() && q2 == q, "complement formulation agrees");
      largest = std::max(largest, Reference::degree(q));
      quotientPolys.push_back(q);
    }
    require(largest == 14, "the interior cubic reaches its exact bound");
    // The last-row assertion reading the next row wraps to row 0: its
    // numerator vanishes at g^(n-1), where T(g X) takes T's row-0 value.
    require(view.assertions[8].bound.begin == n - 1 &&
                f.eval(honest[8], points[n - 1]) == 0 &&
                f.eval(inputsFor(data.witness)[4], points[n - 1]) ==
                    f.parse(data.witness[0]),
            "cyclic wrap of the next-row read on the last row");
    // Coefficient blocks of length n reproduce the largest quotient at a
    // point outside the domain.
    const auto &q6 = quotientPolys[6];
    const uint64_t zeta = f.parse("123456789");
    require(f.pow(zeta, n) != 1, "evaluation point off the domain");
    uint64_t split = 0;
    for (uint64_t k = 0; k < view.quotientChunks; ++k) {
      const size_t lo = std::min<size_t>(k * n, q6.size()),
                   hi = std::min<size_t>((k + 1) * n, q6.size());
      Reference::Poly block(q6.begin() + lo, q6.begin() + hi);
      split = f.add(split, f.mul(f.pow(zeta, k * n), f.eval(block, zeta)));
    }
    require(q6.size() == 15 && split == f.eval(q6, zeta),
            "two coefficient blocks reproduce the degree-14 quotient");
    // One changed witness cell breaks divisibility somewhere.
    auto changed = data.witness;
    changed[3 * 4 + 0] = changed[3 * 4 + 0] == "7" ? "8" : "7";
    const auto mutated = numerators(changed);
    unsigned broken = 0;
    for (size_t i = 0; i < view.assertions.size(); ++i) {
      const auto &bound = view.assertions[i].bound;
      std::vector<uint64_t> rows(points.begin() + bound.begin,
                                 points.begin() + bound.end);
      if (!f.divide(mutated[i], f.vanishing(rows)).second.empty())
        ++broken;
    }
    require(broken > 0, "a changed cell leaves a nonzero remainder");
  });
  return cases.result();
}
