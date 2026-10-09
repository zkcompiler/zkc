#include "Semantics.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/Bundle.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language::detail {
namespace {
bool ringProjection(StringRef member) {
  return member == "Inputs" || member == "Outputs" || member == "Degree";
}
bool bundleProjection(StringRef member) {
  return member == "Tables" || member == "Publics" || member == "Channels";
}
} // namespace
const Asset *Semantics::capturedAsset(const Type &term, Span span) {
  if (term.kind != Type::Kind::Asset || term.symbolic) {
    fail("source.asset-reference", "expected a closed asset term", span);
    return nullptr;
  }
  if (!charge(assets.size() + 1, span))
    return nullptr;
  auto found = llvm::find_if(assets, [&](const Asset &asset) {
    return asset.identity() == term.domain;
  });
  if (found == assets.end()) {
    fail("source.asset-reference", "captured asset is absent", span);
    return nullptr;
  }
  return &*found;
}
std::optional<Type> Semantics::assetProjection(const Type &base,
                                               StringRef member, Span span) {
  auto refuse = [&](const Twine &detail) -> std::optional<Type> {
    fail("source.asset-projection", detail, span);
    return {};
  };
  if (base.kind != Type::Kind::Asset)
    return refuse("projection requires an asset term");
  if (!charge(member.size() + 1, span))
    return {};
  bool ring = assetSort(base) == "Ring";
  if (ring ? !ringProjection(member) : !bundleProjection(member))
    return refuse("unknown " + assetSort(base) + " projection: " + member);
  Type result(Type::Kind::Natural);
  if (base.symbolic) {
    // A generic term's fact is a distinct factor that closure substitutes
    // from the captured asset; both sorts use the same mechanism.
    auto factor = Natural::projection(base.domain, member);
    if (!factor)
      return accept(factor.takeError(), span), std::optional<Type>{};
    result.dimension = std::move(*factor);
    result.symbolic = true;
    return result;
  }
  const auto *asset = capturedAsset(base, span);
  if (!asset)
    return {};
  uint64_t value = 0;
  if (const auto *arena = asset->ring()) {
    if (!charge(arena->outputs().size() + 1, span))
      return {};
    if (member == "Inputs")
      value = arena->inputs().size();
    else if (member == "Outputs")
      value = arena->outputs().size();
    else {
      // Unit-weight output degrees are formation facts, saturated one above
      // the arena limit; a saturated fact is not a number.
      for (auto output : arena->outputs())
        value = std::max<uint64_t>(value, arena->facts()[output].degree);
      if (value > ring::Limits::degree)
        return refuse("expression degree exceeds the arena limit");
    }
  } else {
    const auto *bundle = asset->bundle();
    if (!bundle)
      return refuse("asset kind has no projections");
    value = member == "Tables"     ? bundle->tables().size()
            : member == "Channels" ? bundle->channels().size()
                                   : bundle->publics().size();
  }
  result.dimension = Natural::constant(value);
  return result;
}
} // namespace zkc::language::detail
