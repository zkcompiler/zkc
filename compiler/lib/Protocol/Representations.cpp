#include "zkc/Protocol/Representations.h"
#include "zkc/Target/Json.h"
#include "llvm/Support/Errc.h"
#include <algorithm>
#include <set>
#include <utility>

using namespace llvm;
namespace zkc::protocol {
namespace {
Error refuse(StringRef code) { return zkc::error(code); }
} // namespace

EdwardsScalarModule::EdwardsScalarModule(NominalDomain scalar,
                                         NominalDomain group,
                                         DomainRepresentation repr)
    : scalar(std::move(scalar)), group(std::move(group)),
      repr(std::move(repr)) {}
Expected<EdwardsScalarModule>
EdwardsScalarModule::admit(const DomainCatalog &catalog, StringRef group,
                           StringRef representation, StringRef scalar) {
  // Closed adapter law, corresponding to the invariant of SubgroupEdwards.
  // A raw Edwards domain with a claimed ScalarAction flag is still refused.
  if (group != "edwards25519.prime-subgroup" ||
      scalar != "edwards25519.scalar" ||
      representation != "dalek.edwards-prime-subgroup/1")
    return refuse("representation.unsupported-scalar-module");
  const auto *g = catalog.domain(group);
  const auto *s = catalog.domain(scalar);
  const auto *r = catalog.representation("group", group, representation);
  if (!g || !s || !r || g->sort != "Group" || s->sort != "Field" ||
      s->modulus != "7237005577332262213973186563042994240857116359379907606001"
                    "950938285454250989" ||
      catalog.associatedIdentity(group, "Scalar") != scalar ||
      !catalog.hasFact("ScalarAction", {group.str()}) ||
      !catalog.hasFact("Field", {scalar.str()}))
    return refuse("representation.missing-module-domain");
  return EdwardsScalarModule(*s, *g, *r);
}

OrderedBooleanDomain::OrderedBooleanDomain(std::vector<uint32_t> axes,
                                           uint64_t extent)
    : orderedAxes(std::move(axes)), valueExtent(extent) {}
Expected<OrderedBooleanDomain>
OrderedBooleanDomain::admit(std::vector<uint32_t> axes, uint64_t valueExtent) {
  if (axes.size() >= 64)
    return refuse("representation.dimension-overflow");
  if (std::set<uint32_t>(axes.begin(), axes.end()).size() != axes.size())
    return refuse("representation.duplicate-axis");
  if (valueExtent != (uint64_t(1) << axes.size()))
    return refuse("representation.shape-mismatch");
  return OrderedBooleanDomain(std::move(axes), valueExtent);
}

BooleanFold::BooleanFold(OrderedBooleanDomain source,
                         OrderedBooleanDomain target, uint32_t axis,
                         FoldConvention order)
    : input(std::move(source)), output(std::move(target)), selectedAxis(axis),
      order(order) {}
Expected<BooleanFold> BooleanFold::admit(const OrderedBooleanDomain &source,
                                         uint32_t axis, FoldConvention order) {
  auto axes = source.axes();
  if (order != FoldConvention::Adjacent && order != FoldConvention::HalfFirst)
    return refuse("representation.unsupported-fold");
  if (axes.empty())
    return refuse("representation.axis-mismatch");
  const auto position = order == FoldConvention::Adjacent ? 0 : axes.size() - 1;
  if (axes[position] != axis)
    return refuse("representation.axis-mismatch");
  axes.erase(axes.begin() + position);
  auto target =
      OrderedBooleanDomain::admit(std::move(axes), source.extent() / 2);
  if (!target)
    return target.takeError();
  return BooleanFold(source, std::move(*target), axis, order);
}
Expected<std::pair<uint64_t, uint64_t>> BooleanFold::pair(uint64_t row) const {
  if (row >= output.extent())
    return refuse("representation.index-out-of-bounds");
  if (order == FoldConvention::Adjacent)
    return std::make_pair(2 * row, 2 * row + 1);
  return std::make_pair(row, row + output.extent());
}

BooleanAxisMap::BooleanAxisMap(OrderedBooleanDomain source,
                               OrderedBooleanDomain target)
    : input(std::move(source)), output(std::move(target)) {}
Expected<BooleanAxisMap>
BooleanAxisMap::admit(const OrderedBooleanDomain &source,
                      const OrderedBooleanDomain &target) {
  auto a = source.axes(), b = target.axes();
  std::sort(a.begin(), a.end());
  std::sort(b.begin(), b.end());
  if (a != b)
    return refuse("representation.invalid-permutation");
  return BooleanAxisMap(source, target);
}
Expected<uint64_t> BooleanAxisMap::sourceIndex(uint64_t targetIndex) const {
  if (targetIndex >= output.extent())
    return refuse("representation.index-out-of-bounds");
  uint64_t result = 0;
  for (size_t i = 0; i < output.axes().size(); ++i) {
    const auto source =
        std::find(input.axes().begin(), input.axes().end(), output.axes()[i]);
    const auto bit = source - input.axes().begin();
    result |= ((targetIndex >> i) & 1) << bit;
  }
  return result;
}
Expected<uint64_t> rotatedBooleanRow(const OrderedBooleanDomain &domain,
                                     uint64_t shift, uint64_t row) {
  if (row >= domain.extent())
    return refuse("representation.index-out-of-bounds");
  shift %= domain.extent();
  const auto gap = domain.extent() - shift;
  return row >= gap ? row - gap : row + shift;
}
} // namespace zkc::protocol
