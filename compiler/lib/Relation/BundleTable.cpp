#include "BundleInternal.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MathExtras.h"
#include <set>

using namespace llvm;
namespace zkc::relation {
using namespace bundle;

namespace {
/// Field compatibility of every arena node an assertion needs, visited
/// through the arena's own evaluation order without arithmetic.
struct CarrierCheck {
  StringRef carrier, base;
  Expected<char> ok(StringRef field) const {
    if (field == carrier || (!base.empty() && field == base))
      return char(0);
    return zkc::error("relation-table-carrier", field);
  }
  Expected<char> input(uint32_t, StringRef field) { return ok(field); }
  Expected<char> constant(StringRef field, StringRef) { return ok(field); }
  Expected<char> add(StringRef field, char, char) { return ok(field); }
  Expected<char> mul(StringRef field, char, char) { return ok(field); }
  Expected<char> neg(StringRef field, char) { return ok(field); }
  Expected<char> embed(StringRef, StringRef target, char) { return ok(target); }
};
std::vector<int32_t> readOffsets(const BundleOutputFact &fact) {
  std::vector<int32_t> result;
  for (const auto &read : fact.reads)
    result.push_back(read.offset);
  return result;
}
} // namespace

Expected<BundleTableView> bundleTableView(const Bundle &bundle, uint32_t table,
                                          StringRef carrier) {
  if (table >= bundle.tables().size())
    return zkc::error("relation-table-index");
  auto shape = presentation(carrier);
  if (!shape) {
    consumeError(shape.takeError());
    return zkc::error("relation-table-carrier", carrier);
  }
  const auto &t = bundle.tables()[table];
  BundleTableView view;
  view.table = table;
  view.field = carrier.str();
  view.optional = t.optional;
  view.height = t.height;
  view.readModel = t.readModel;
  view.publicSlots = bundle.publics().size();
  view.coordinates = shape->degree;
  for (const auto &slot : bundle.publics())
    if (slot.field != carrier)
      return zkc::error("relation-table-carrier", slot.name);
  for (const auto &group : t.groups) {
    if (group.field != carrier)
      return zkc::error("relation-table-carrier", t.name + "." + group.name);
    auto &width =
        group.authority == BundleAuthority::Witness  ? view.witnessWidth
        : group.authority == BundleAuthority::Config ? view.configWidth
                                                     : view.publicWidth;
    width += group.width; // At most 256 groups of width 65,536.
  }
  const auto &facts = bundle.facts()[table];
  std::set<uint32_t> outputs;
  for (const auto &assertion : t.assertions) {
    const auto &fact = facts[assertion.output];
    if (fact.field != carrier)
      return zkc::error("relation-table-carrier", t.name);
    view.degree = std::max(view.degree, fact.degree);
    outputs.insert(assertion.output);
  }
  view.assertions = t.assertions.size();
  CarrierCheck check{carrier, shape->degree == 1 ? StringRef() : shape->prime};
  std::vector<uint32_t> positions(outputs.begin(), outputs.end());
  if (auto visited = t.arena.evaluate<char>(positions, check); !visited)
    return visited.takeError();
  return view;
}

// TODO: derive these premises from the shared Bundle polynomial analysis once
// it is available, so the compiler and that analysis cannot drift.
Error checkBundlePolynomialTable(const Bundle &bundle, uint32_t table,
                                 StringRef carrier) {
  if (table >= bundle.tables().size())
    return zkc::error("relation-table-index");
  auto shape = presentation(carrier);
  if (!shape) {
    consumeError(shape.takeError());
    return zkc::error("relation-table-carrier", carrier);
  }
  CarrierCheck check{carrier, shape->degree == 1 ? StringRef() : shape->prime};
  const auto &t = bundle.tables()[table];
  for (const auto &slot : bundle.publics())
    if (auto ok = check.ok(slot.field); !ok)
      return withDetail(ok.takeError(), slot.name);
  for (const auto &group : t.groups)
    if (auto ok = check.ok(group.field); !ok)
      return withDetail(ok.takeError(), t.name + "." + group.name);
  std::set<uint32_t> outputs;
  for (const auto &assertion : t.assertions)
    outputs.insert(assertion.output);
  std::vector<uint32_t> positions(outputs.begin(), outputs.end());
  if (auto visited = t.arena.evaluate<char>(positions, check); !visited)
    return visited.takeError();
  // The view's domain is the multiplicative subgroup of order `height`. On
  // it a rotation by `offset mod height` realizes both a cyclic read and a
  // finite read whose window is checked at that height.
  const uint64_t least = std::max<uint64_t>(t.height.min, 2);
  if (PowerOf2Ceil(least) > t.height.max)
    return zkc::error("bundle-polynomial-two-adic", t.name);
  return Error::success();
}

Error checkBundleTableReference(const Bundle &bundle, StringRef contract,
                                uint32_t table, StringRef carrier) {
  if (contract == "relation.table_rows") {
    auto view = bundleTableView(bundle, table, carrier);
    return view ? Error::success() : view.takeError();
  }
  if (contract == "relation.table_shape" ||
      contract == "relation.table_input" ||
      contract == "relation.table_scope" || contract == "relation.table_point")
    return checkBundlePolynomialTable(bundle, table, carrier);
  return zkc::error("relation-table-contract", contract);
}

Expected<BundleTableLengths>
bundleTableLengths(const Bundle &bundle, const BundleTableView &reference,
                   uint32_t height) {
  // Re-derive facts from the admitted Bundle. The public descriptive view is
  // not an authority for lengths or resource bounds.
  auto checked = bundleTableView(bundle, reference.table, reference.field);
  if (!checked)
    return checked.takeError();
  const auto &view = *checked;
  const auto &t = bundle.tables()[view.table];
  const auto &policy = t.height;
  if (height < policy.min || height > policy.max ||
      (policy.powerOfTwo && !isPowerOf2_32(height)))
    return zkc::error("bundle-height", t.name);
  // Declared shape is bounded before any length is compared.
  const uint64_t rows = height, d = view.coordinates;
  BundleTableLengths lengths;
  lengths.witness = rows * view.witnessWidth;
  lengths.configuration = rows * view.configWidth;
  lengths.publicData = uint64_t(view.publicSlots) + rows * view.publicWidth;
  if (d * (lengths.witness + lengths.configuration + lengths.publicData) >
      BundleLimits::coordinates)
    return zkc::error("bundle-data-limit", t.name);
  // Every read domain is checked from syntax before any arithmetic, so a
  // product with zero cannot hide an undefined read.
  const auto &facts = bundle.facts()[view.table];
  for (const auto &assertion : t.assertions)
    if (auto error = windowAt(assertion.scope, t.readModel, height,
                              readOffsets(facts[assertion.output])))
      return withDetail(std::move(error), t.name);
  const uint64_t assertions = t.assertions.size();
  if (assertions && rows * (t.arena.nodes().size() + t.arena.inputs().size() +
                            assertions + 1) >
                        BundleLimits::work)
    return zkc::error("bundle-work-limit", t.name);
  lengths.results = rows * assertions;
  if (lengths.results > BundleLimits::resultRecords ||
      lengths.results * d > BundleLimits::resultCoordinates)
    return zkc::error("bundle-result-limit", t.name);
  return lengths;
}

Expected<BundleTableData>
sliceBundleTableData(const Bundle &bundle, const BundleTableView &view,
                     const BundleConfiguration &config,
                     const BundleInstance &instance,
                     const BundleWitness &witness) {
  if (auto error = bundle.admit(config, instance, witness))
    return error;
  if (view.table >= bundle.tables().size())
    return zkc::error("relation-table-index");
  const auto &t = bundle.tables()[view.table];
  const auto &ins = instance.tables[view.table];
  if (!ins.present)
    return zkc::error("relation-table-absent", t.name);
  BundleTableData data;
  switch (t.height.authority) {
  case BundleHeightAuthority::Fixed:
    data.height = t.height.min;
    break;
  case BundleHeightAuthority::Config:
    data.height = *config.tables[view.table].height;
    break;
  case BundleHeightAuthority::Instance:
    data.height = *ins.height;
    break;
  }
  auto lengths = bundleTableLengths(bundle, view, data.height);
  if (!lengths)
    return lengths.takeError();
  for (const auto &slot : instance.publics)
    llvm::append_range(data.publicData, slot);
  size_t next[3] = {0, 0, 0};
  for (const auto &group : t.groups) {
    switch (group.authority) {
    case BundleAuthority::Config:
      llvm::append_range(data.configuration,
                         config.tables[view.table].groups[next[0]++]);
      break;
    case BundleAuthority::Public:
      llvm::append_range(data.publicData, ins.groups[next[1]++]);
      break;
    case BundleAuthority::Witness:
      llvm::append_range(data.witness,
                         (*witness.tables[view.table])[next[2]++]);
      break;
    }
  }
  return data;
}

} // namespace zkc::relation
