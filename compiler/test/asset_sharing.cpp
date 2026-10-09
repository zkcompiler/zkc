#include "support/NativeCases.h"
#include "zkc/Compiler/AssetSharing.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::relation;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<bool> checked(Error failure) {
  if (failure)
    return std::move(failure);
  return true;
}
zkc::ring::Expression repeated() {
  using N = zkc::ring::Node;
  return take(zkc::ring::Expression::create(
      {{"koala-bear"}},
      {N::slot(0), N::mul(0, 0), N::slot(0), N::mul(2, 2), N::add(1, 3)}, {4}));
}
Asset captured(const Bundle &bundle) {
  return take(Asset::read(
      {"trace", "relation-bundle-json", zkc::printJson(bundle.encode()), {}}));
}
Bundle relation() {
  BundleTable table{"trace",
                    false,
                    {BundleHeightAuthority::Fixed, 2, 2, false},
                    BundleReadModel::Finite,
                    {{"values", BundleAuthority::Witness, "koala-bear", 1}},
                    repeated(),
                    {BundleInput::read(0, 0, 0)},
                    {{0, {BundleScopeKind::All, 0, 0}}},
                    {}};
  return take(Bundle::create({}, {}, {std::move(table)}));
}
BundleEvaluation evaluate(const Bundle &bundle) {
  BundleConfiguration configuration;
  configuration.relation = bundle.identity().str();
  configuration.tables.resize(1);
  BundleInstance instance;
  instance.relation = bundle.identity().str();
  instance.tables.resize(1);
  BundleWitness witness;
  witness.relation = bundle.identity().str();
  witness.tables.push_back(std::vector<BundleColumns>{{"2", "3"}});
  return take(bundle.evaluate(configuration, instance, witness));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("ring asset sharing returns a fresh checked definition", [] {
    auto original = take(Asset::read(
        {"product", "ring-json", zkc::printJson(repeated().encode()), {}}));
    auto shared = take(shareAsset(original));
    require(shared.changed && shared.asset.identity() != original.identity(),
            "changed expression reused its structural identity");
    require(original.ring()->nodes().size() == 5 &&
                shared.asset.ring()->nodes().size() == 3,
            "original was mutated or sharing did not reduce work");
    take(checked(checkAssetSharing(original, shared.asset, shared.nodeMaps)));
    require(!take(shareAsset(shared.asset)).changed,
            "sharing is not idempotent");
    shared.nodeMaps[0][0] = 1;
    refuses(checked(checkAssetSharing(original, shared.asset, shared.nodeMaps)),
            "ring-sharing-node");
  });
  cases.run("bundle sharing preserves bound trace results and facts", [] {
    auto original = captured(relation());
    auto shared = take(shareAsset(original));
    require(shared.changed, "bundle arena was not shared");
    auto before = evaluate(*original.bundle());
    auto after = evaluate(*shared.asset.bundle());
    require(before.residuals.size() == 2 && after.residuals.size() == 2 &&
                before.residuals[0].value == BundleColumns{"8"} &&
                before.residuals[1].value == BundleColumns{"18"},
            "independent trace residual expectations differ");
    for (unsigned i = 0; i < before.residuals.size(); ++i)
      require(before.residuals[i].value == after.residuals[i].value &&
                  before.residuals[i].row == after.residuals[i].row,
              "shared binding changed evaluation");
    const auto &a = original.bundle()->facts()[0][0];
    const auto &b = shared.asset.bundle()->facts()[0][0];
    require(a.degree == b.degree && a.reads == b.reads &&
                a.publics == b.publics,
            "bundle analysis changed");
    refuses(checked(checkAssetSharing(original, shared.asset, {})),
            "asset-sharing-shape");
  });
  cases.run(
      "checker rejects changed scopes and authority around equal arenas", [] {
        auto original = captured(relation());
        auto shared = take(shareAsset(original));
        for (bool changeAuthority : {false, true}) {
          auto tables =
              std::vector<BundleTable>(shared.asset.bundle()->tables().begin(),
                                       shared.asset.bundle()->tables().end());
          if (changeAuthority)
            tables[0].groups[0].authority = BundleAuthority::Config;
          else
            tables[0].assertions[0].scope.kind = BundleScopeKind::First;
          auto changed =
              captured(take(Bundle::create({}, {}, std::move(tables))));
          refuses(
              checked(checkAssetSharing(original, changed, shared.nodeMaps)),
              "asset-sharing-context");
        }
      });
  cases.run("checker does not identify different asset kinds", [] {
    auto ring = take(Asset::read(
        {"product", "ring-json", zkc::printJson(repeated().encode()), {}}));
    refuses(checked(checkAssetSharing(ring, captured(relation()), {})),
            "asset-sharing-kind");
  });
  return cases.result();
}
