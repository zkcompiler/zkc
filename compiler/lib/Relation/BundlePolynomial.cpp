#include "zkc/Relation/BundlePolynomial.h"
#include "BundleInternal.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/APInt.h"
#include "llvm/Support/MathExtras.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::relation {
using namespace bundle;

namespace {
/// Whether rows 0 .. size-1 can be the consecutive powers of a root of exact
/// order `size` in the carrier's prime subfield: the carrier has the installed
/// two-adic capability, the size is a power of two and it divides the order
/// of the prime subfield's multiplicative group. Only then does a cyclic read
/// at offset k wrap as T(g^k X) on every row.
bool twoAdicDomain(StringRef carrier, const Presentation &shape,
                   uint32_t size) {
  if (size < 2 || !isPowerOf2_32(size))
    return false;
  if (!protocol::installedDomains().hasFact("TwoAdicField", {carrier.str()}))
    return false;
  StringRef modulus = protocol::fieldModulus(shape.prime);
  if (modulus.empty())
    return false;
  const unsigned bits = APInt::getBitsNeeded(modulus, 10) + 1;
  APInt order(bits, modulus, 10);
  order -= 1;
  return order.urem(APInt(bits, size)).isZero();
}
std::vector<int32_t> readOffsets(const BundleOutputFact &fact) {
  std::vector<int32_t> result;
  for (const auto &read : fact.reads)
    result.push_back(read.offset);
  return result;
}
} // namespace

Expected<AIRPolynomialParameters> twoAdicPolynomialParameters(uint32_t height) {
  if (height < 2 || height > AIRPolynomialParameters::sizeLimit ||
      !isPowerOf2_32(height))
    return zkc::error("bundle-polynomial-two-adic");
  return AIRPolynomialParameters{height, height, height - 1};
}

Expected<BundlePolynomialView>
analyzeBundlePolynomials(const Bundle &bundle, uint32_t table,
                         StringRef carrier,
                         AIRPolynomialParameters parameters) {
  auto checked = bundleTableView(bundle, table, carrier);
  if (!checked)
    return checked.takeError();
  if (auto error = checkAIRPolynomialParameters(parameters))
    return error;
  const auto &t = bundle.tables()[table];
  const auto &policy = t.height;
  const uint32_t height = parameters.height;
  if (height < policy.min || height > policy.max ||
      (policy.powerOfTwo && !isPowerOf2_32(height)))
    return zkc::error("bundle-height", t.name);
  auto shape = presentation(carrier);
  if (!shape)
    return shape.takeError();
  // Padding a finite table never adds active rows, so the law of AIRPolynomial
  // applies unchanged. A cyclic table has no padding interpretation: a wrapped
  // read on row i denotes row (i + k) mod height, which T(g^k X) realizes only
  // when the row points are the whole order-height subgroup.
  const bool twoAdic =
      parameters.domainSize == height && twoAdicDomain(carrier, *shape, height);
  if (t.readModel == BundleReadModel::Cyclic && !twoAdic)
    return zkc::error("bundle-polynomial-domain", t.name);
  // Every read domain is checked from syntax before any bound is derived.
  const auto &facts = bundle.facts()[table];
  for (const auto &assertion : t.assertions)
    if (auto error = windowAt(assertion.scope, t.readModel, height,
                              readOffsets(facts[assertion.output])))
      return withDetail(std::move(error), t.name);

  BundlePolynomialView view;
  view.relation = bundle.identity().str();
  view.table = table;
  view.name = t.name;
  view.field = carrier.str();
  view.coordinates = checked->coordinates;
  view.optional = t.optional;
  view.heightPolicy = policy;
  view.readModel = t.readModel;
  view.parameters = parameters;
  view.profile = twoAdic && parameters.traceDegree == height - 1
                     ? BundlePolynomialProfile::TwoAdicNatural
                     : BundlePolynomialProfile::General;
  for (const auto &group : t.groups)
    view.groups.push_back(
        {group.name, group.authority, group.field, group.width, {}});
  view.bindings = t.inputs;
  // Facts are unioned once per distinct active output; assertions may share
  // an output. The total is bounded by the Bundle's retained input facts.
  std::set<uint32_t> activeOutputs;
  std::set<BundleRead> reads;
  std::set<uint32_t> publics;
  for (const auto &assertion : t.assertions) {
    const auto &fact = facts[assertion.output];
    auto [begin, end] = scopeRows(assertion.scope, height);
    auto bound = scopedQuotientBound(parameters, begin, end, fact.degree);
    if (bound.active()) {
      ++view.activeAssertions;
      if (activeOutputs.insert(assertion.output).second) {
        reads.insert(fact.reads.begin(), fact.reads.end());
        publics.insert(fact.publics.begin(), fact.publics.end());
      }
      if (bound.quotientDegree) {
        view.maxQuotientDegree =
            std::max(view.maxQuotientDegree.value_or(0), *bound.quotientDegree);
        view.quotientChunks = std::max(
            view.quotientChunks,
            quotientChunkCount(*bound.quotientDegree, parameters.domainSize));
      }
    }
    view.assertions.push_back(
        {assertion.output, assertion.scope, fact.degree, bound});
  }
  view.reads.assign(reads.begin(), reads.end());
  view.publics.assign(publics.begin(), publics.end());
  // Reads are ordered by (group, offset, column), so each group's offsets
  // arrive sorted.
  for (const auto &read : view.reads) {
    auto &offsets = view.groups[read.group].offsets;
    if (offsets.empty() || offsets.back() != read.offset)
      offsets.push_back(read.offset);
  }
  view.arena = t.arena.identity();
  return view;
}

Expected<const ring::Expression *>
bundlePolynomialArena(const Bundle &bundle, const BundlePolynomialView &view) {
  if (view.relation != bundle.identity() ||
      view.table >= bundle.tables().size())
    return zkc::error("bundle-polynomial-relation");
  const auto &arena = bundle.tables()[view.table].arena;
  if (arena.identity() != view.arena)
    return zkc::error("bundle-polynomial-relation");
  return &arena;
}

json::Value BundlePolynomialView::encode() const {
  json::Array groupList, bindingList, publicList, readList, assertionList;
  for (const auto &group : groups) {
    json::Array offsetList;
    for (auto offset : group.offsets)
      offsetList.push_back(printOffset(offset));
    groupList.push_back(
        json::Object{{"name", group.name},
                     {"authority", authorityName(group.authority)},
                     {"field", group.field},
                     {"width", group.width},
                     {"offsets", std::move(offsetList)}});
  }
  for (const auto &input : bindings)
    bindingList.push_back(input.kind == BundleInput::Kind::Public
                              ? json::Array{"public", input.index}
                              : json::Array{"read", input.index,
                                            printOffset(input.offset),
                                            input.column});
  for (auto slot : publics)
    publicList.push_back(slot);
  for (const auto &read : reads)
    readList.push_back(
        json::Array{read.group, printOffset(read.offset), read.column});
  for (const auto &assertion : assertions) {
    const auto &c = assertion.bound;
    assertionList.push_back(json::Object{
        {"output", assertion.output},
        {"scope", encodeScope(assertion.scope)},
        {"degree", assertion.degree},
        {"active_begin", c.begin},
        {"active_end", c.end},
        {"active", c.active()},
        {"selector_degree", c.selectorDegree},
        {"numerator_degree", c.numeratorDegree},
        {"quotient_degree", c.quotientDegree ? json::Value(*c.quotientDegree)
                                             : json::Value(nullptr)}});
  }
  return json::Object{
      {"schema", "zkc.relation-bundle-polynomial-analysis/0"},
      {"relation", relation},
      {"table", table},
      {"name", name},
      {"carrier", field},
      {"coordinates", coordinates},
      {"optional", optional},
      {"height_policy", encodeHeight(heightPolicy)},
      {"read_model",
       readModel == BundleReadModel::Cyclic ? "cyclic" : "finite"},
      {"height", parameters.height},
      {"domain_size", parameters.domainSize},
      {"trace_degree", parameters.traceDegree},
      {"profile", profile == BundlePolynomialProfile::TwoAdicNatural
                      ? "two-adic-natural"
                      : "general"},
      {"groups", std::move(groupList)},
      {"bindings", std::move(bindingList)},
      {"publics", std::move(publicList)},
      {"reads", std::move(readList)},
      {"assertions", std::move(assertionList)},
      {"active_assertions", activeAssertions},
      {"max_quotient_degree", maxQuotientDegree
                                  ? json::Value(*maxQuotientDegree)
                                  : json::Value(nullptr)},
      {"quotient_chunks", quotientChunks},
      {"arena", arena}};
}

} // namespace zkc::relation
