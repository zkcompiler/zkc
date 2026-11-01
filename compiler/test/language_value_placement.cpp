#include "support/NativeCases.h"
#include "zkc/Language/ValuePlacement.h"
#include <algorithm>

using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
using zkc::test::take;

namespace {
ValuePlacement sources() {
  return ProductPlacement{"TwoSources<F>",
                          {0, 1, 2},
                          {OraclePlacement{0, {2}}, OraclePlacement{1, {2}},
                           DataPlacement{{2}},
                           ProductPlacement{"PrivateEmpty<F>", {1, 2}, {}}}};
}
void refuses(const ValuePlacement &value, unsigned participants, StringRef code,
             uint64_t work = 10000, unsigned depth = 16) {
  auto error = validatePlacement(value, participants, work, depth);
  require(bool(error), "invalid placement was admitted");
  require(namesIdentifier(toString(std::move(error)), code),
          "placement refusal has wrong diagnostic");
}
ValuePlacement remap(const ValuePlacement &value, ArrayRef<unsigned> mapping,
                     unsigned participants) {
  uint64_t remaining = 10000;
  return take(substitutePlacement(value, mapping, participants, remaining, 16));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "role permutations preserve exact fields and empty nominal children", [] {
        auto original = sources();
        std::vector<unsigned> mapping{0, 1, 2};
        do {
          auto value = remap(original, mapping, 3);
          const auto &product = std::get<ProductPlacement>(value.value);
          require(product.arguments == mapping,
                  "telescope substitution was sorted into a role set");
          require(product.fields[0] == ValuePlacement(OraclePlacement{
                                           mapping[0], {mapping[2]}}) &&
                      product.fields[1] == ValuePlacement(OraclePlacement{
                                               mapping[1], {mapping[2]}}),
                  "independent holders were replaced by an aggregate family");
          require(product.fields[3] ==
                      ValuePlacement(ProductPlacement{
                          "PrivateEmpty<F>", {mapping[1], mapping[2]}, {}}),
                  "empty nominal child or its ordered application disappeared");
          std::vector<unsigned> inverse(3);
          for (unsigned i = 0; i < 3; ++i)
            inverse[mapping[i]] = i;
          require(remap(value, inverse, 3) == original,
                  "permutation round trip changed placed identity");
        } while (std::next_permutation(mapping.begin(), mapping.end()));
      });
  cases.run("same participant union does not identify a product", [] {
    auto original = sources();
    auto swapped = original;
    auto &product = std::get<ProductPlacement>(swapped.value);
    std::swap(product.fields[0], product.fields[1]);
    require(swapped != original, "equal role union erased field association");
    swapped = original;
    std::get<ProductPlacement>(swapped.value).fields.pop_back();
    require(swapped != original, "empty field was erased from identity");
    swapped = original;
    std::get<ProductPlacement>(swapped.value).instance = "TwoSources<G>";
    require(swapped != original, "phantom instance was erased from identity");
  });
  cases.run("set canonicalization is distinct from ordered applications", [] {
    auto value = remap(DataPlacement{{0, 2}}, {2, 1, 0}, 3);
    require(value == ValuePlacement(DataPlacement{{0, 2}}),
            "substitution did not canonicalize a data role set");
    value = remap(OraclePlacement{0, {1, 2}}, {2, 1, 0}, 3);
    require(value == ValuePlacement(OraclePlacement{2, {0, 1}}),
            "substitution changed holder/receiver meaning");
  });
  cases.run("invalid role families and escaped fields refuse", [] {
    refuses(DataPlacement{{}}, 3, "source.roles");
    refuses(DataPlacement{{1, 0}}, 3, "source.roles");
    refuses(DataPlacement{{0, 0}}, 3, "source.roles");
    refuses(OraclePlacement{1, {0, 1}}, 3, "source.roles");
    refuses(OraclePlacement{3, {0}}, 3, "source.roles");
    refuses(ProductPlacement{"R", {0, 1}, {DataPlacement{{2}}}}, 3,
            "source.roles");
    refuses(ProductPlacement{"R", {0, 1}, {OraclePlacement{2, {1}}}}, 3,
            "source.roles");
    refuses(ProductPlacement{"Outer",
                             {0, 1, 2},
                             {ProductPlacement{
                                 "Inner", {0, 1}, {DataPlacement{{2}}}}}},
            3, "source.roles");
    refuses(ProductPlacement{"R", {0, 0}, {}}, 3, "source.roles");
    refuses(ProductPlacement{"", {0, 1}, {}}, 3, "source.placement");
  });
  cases.run(
      "bad substitutions and bounded work cannot produce a partial value", [] {
        auto original = sources();
        for (const std::vector<unsigned> &mapping :
             {std::vector<unsigned>{0, 0, 2}, {0, 1}, {0, 1, 3}}) {
          uint64_t remaining = 10000;
          auto result =
              substitutePlacement(original, mapping, 3, remaining, 16);
          require(!result, "invalid role substitution was admitted");
          require(namesIdentifier(toString(result.takeError()), "source.roles"),
                  "invalid substitution has wrong diagnostic");
          require(original == sources(),
                  "failed substitution mutated its input");
        }
        refuses(original, 3, "source.limit", 1);
        refuses(original, 3, "source.limit", 10000, 1);
        uint64_t remaining = 1;
        auto result =
            substitutePlacement(original, {0, 1, 2}, 3, remaining, 16);
        require(!result, "substitution ignored the caller's work budget");
        consumeError(result.takeError());
      });
  cases.run(
      "late budget exhaustion does not publish a partial substitution", [] {
        auto original = sources();
        bool completed = false;
        for (uint64_t budget = 0; budget < 1000; ++budget) {
          uint64_t remaining = budget;
          auto result =
              substitutePlacement(original, {0, 1, 2}, 3, remaining, 16);
          require(original == sources(),
                  "budget refusal changed the input tree");
          if (result) {
            require(*result == original,
                    "complete identity substitution differs");
            completed = true;
            break;
          }
          require(
              namesIdentifier(toString(result.takeError()), "source.limit"),
              "a valid placement failed for a reason other than its budget");
        }
        require(completed, "bounded fixture never completed substitution");
      });
  return cases.result();
}
