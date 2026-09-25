#include "zkc/Protocol/Representations.h"
#include <cstdlib>
#include <iostream>
#include <limits>
using namespace zkc::protocol;
unsigned checks = 0;
void check(bool ok, const char *label) {
  ++checks;
  if (!ok) {
    std::cerr << label << '\n';
    std::exit(1);
  }
}
template <class T> void rejects(llvm::Expected<T> result, const char *code) {
  check(!result, "expected refusal");
  check(llvm::toString(result.takeError()) == code, "refusal code");
}
int main() {
  auto source = OrderedBooleanDomain::admit({10, 20}, 4);
  check(bool(source), "source domain");
  auto adjacent = BooleanFold::admit(*source, 10, FoldConvention::Adjacent);
  check(bool(adjacent), "adjacent admits");
  check(adjacent->axis() == 10 && adjacent->source().extent() == 4 &&
            adjacent->target().extent() == 2,
        "fold retains domains");
  check(*adjacent->pair(1) == std::make_pair(uint64_t(2), uint64_t(3)),
        "adjacent indices");
  auto half = BooleanFold::admit(*source, 20, FoldConvention::HalfFirst);
  check(bool(half), "half admits");
  check(*half->pair(1) == std::make_pair(uint64_t(1), uint64_t(3)),
        "half indices");
  rejects(BooleanFold::admit(*source, 10, FoldConvention::HalfFirst),
          "representation.axis-mismatch");
  rejects(BooleanFold::admit(*source, 20, FoldConvention::Adjacent),
          "representation.axis-mismatch");
  rejects(BooleanFold::admit(*source, 10, static_cast<FoldConvention>(17)),
          "representation.unsupported-fold");
  rejects(adjacent->pair(2), "representation.index-out-of-bounds");
  auto scalar = OrderedBooleanDomain::admit({}, 1);
  check(bool(scalar), "scalar domain");
  rejects(BooleanFold::admit(*scalar, 0, FoldConvention::Adjacent),
          "representation.axis-mismatch");
  rejects(OrderedBooleanDomain::admit({1, 1}, 4),
          "representation.duplicate-axis");
  rejects(OrderedBooleanDomain::admit(std::vector<uint32_t>(64), 0),
          "representation.dimension-overflow");
  rejects(OrderedBooleanDomain::admit({1, 2}, 3),
          "representation.shape-mismatch");
  auto target = OrderedBooleanDomain::admit({20, 10}, 4);
  auto map = BooleanAxisMap::admit(*source, *target);
  check(bool(map), "map admits");
  for (uint64_t i = 0; i < 4; i++)
    check(*map->sourceIndex(i) == ((i & 1) * 2 + (i >> 1)), "transpose");
  rejects(map->sourceIndex(4), "representation.index-out-of-bounds");
  auto wrong = OrderedBooleanDomain::admit({10, 30}, 4);
  rejects(BooleanAxisMap::admit(*source, *wrong),
          "representation.invalid-permutation");
  rejects(BooleanAxisMap::admit(*source, *scalar),
          "representation.invalid-permutation");
  for (uint64_t i = 0; i < 4; i++)
    check(*rotatedBooleanRow(*source, UINT64_MAX, i) == (i + 3) % 4,
          "rotation modulo");
  rejects(rotatedBooleanRow(*source, 1, 4),
          "representation.index-out-of-bounds");
  std::vector<uint32_t> axes(63);
  for (uint32_t i = 0; i < 63; i++)
    axes[i] = i;
  auto large = OrderedBooleanDomain::admit(axes, uint64_t(1) << 63);
  check(bool(large), "largest extent");
  check(*rotatedBooleanRow(*large, UINT64_MAX, (uint64_t(1) << 63) - 1) ==
            (uint64_t(1) << 63) - 2,
        "no overflow");
  const std::string f = "edwards25519.scalar",
                    g = "edwards25519.prime-subgroup", raw = "edwards25519.raw",
                    r = "dalek.edwards-prime-subgroup/1";
  const std::string modulus = "723700557733226221397318656304299424085711635937"
                              "9907606001950938285454250989";
  auto catalogue =
      DomainCatalog::create({{f, "Field", {}, {"Field"}, modulus},
                             {g, "Group", {{"Scalar", f}}, {"ScalarAction"}},
                             {raw, "Group", {{"Scalar", f}}, {"ScalarAction"}}},
                            {},
                            {{r, "group", g, false, {}},
                             {"dalek.edwards-raw/1", "group", raw, false, {}}});
  check(bool(catalogue), "catalogue admits");
  auto law = EdwardsScalarModule::admit(*catalogue, g, r, f);
  check(bool(law), "module law admits");
  check(law->scalarDomain().identity == f && law->groupDomain().identity == g &&
            law->arithmeticRepresentation().identity == r,
        "law retains actual tuple");
  rejects(EdwardsScalarModule::admit(*catalogue, raw, "dalek.edwards-raw/1", f),
          "representation.unsupported-scalar-module");
  rejects(EdwardsScalarModule::admit(*catalogue, g, r, "ristretto255.scalar"),
          "representation.unsupported-scalar-module");
  rejects(EdwardsScalarModule::admit(*catalogue, g, "dalek.edwards-raw/1", f),
          "representation.unsupported-scalar-module");
  auto missing = DomainCatalog::create(
      {{f, "Field", {}, {"Field"}, modulus}, {g, "Group", {{"Scalar", f}}, {}}},
      {}, {{r, "group", g, false, {}}});
  check(bool(missing), "missing law catalogue");
  rejects(EdwardsScalarModule::admit(*missing, g, r, f),
          "representation.missing-module-domain");
  auto wrongModulus =
      DomainCatalog::create({{f, "Field", {}, {"Field"}, "5"},
                             {g, "Group", {{"Scalar", f}}, {"ScalarAction"}}},
                            {}, {{r, "group", g, false, {}}});
  check(bool(wrongModulus), "wrong modulus catalogue");
  rejects(EdwardsScalarModule::admit(*wrongModulus, g, r, f),
          "representation.missing-module-domain");
  auto empty = DomainCatalog::create({}, {}, {});
  check(bool(empty), "empty catalogue");
  rejects(EdwardsScalarModule::admit(*empty, g, r, f),
          "representation.missing-module-domain");
  std::cout << checks << " C++ representation checks passed\n";
}
