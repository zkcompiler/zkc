#include "zkc/Mathematical/Codec.h"
#include "zkc/Mathematical/Registry.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Relations.h"
#include "zkc/Source/Snapshot.h"

int main() {
  zkc::relation::Constraint row{{{{2, "1"}}, {{3, "1"}}, {{1, "1"}}}};
  auto relation = zkc::relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row});
  if (!relation) {
    llvm::consumeError(relation.takeError());
    return 1;
  }
  zkc::source::Module module;
  module.relations.push_back(
      {{}, "Circuit", std::make_shared<const zkc::relation::R1CS>(*relation)});
  module.relationViews.push_back(
      {{}, "Rows", "Circuit", "multilinear", "specialized", {}});
  if (auto e = zkc::relation::materializeViews(module)) {
    llvm::consumeError(std::move(e));
    return 2;
  }
  auto snapshot = zkc::source::snapshot(module);
  auto encoded = zkc::source::encode(module);
  auto decoded = zkc::source::decode(encoded);
  if (!snapshot || !decoded) {
    if (!snapshot)
      llvm::consumeError(snapshot.takeError());
    if (!decoded)
      llvm::consumeError(decoded.takeError());
    return 3;
  }
  if (auto e = zkc::protocol::admit(*decoded, false)) {
    llvm::consumeError(std::move(e));
    return 4;
  }
  auto reloaded = zkc::source::snapshot(*decoded);
  if (!reloaded) {
    llvm::consumeError(reloaded.takeError());
    return 5;
  }
  if (*snapshot != *reloaded || encoded != zkc::source::encode(*decoded))
    return 6;
  // The lower-only library must retain exact generated-body validation.
  module.functions[1].body->erase(module.functions[1].body->begin());
  auto rejected = zkc::protocol::admit(module, false);
  if (llvm::toString(std::move(rejected)) != "relation-generated-function")
    return 7;

  // The mathematical carrier is available through the same MLIR-free package.
  auto mathematical =
      zkc::mathematical::parseValue(R"({"inputs":[1,2],"ok":true})");
  if (!mathematical) {
    llvm::consumeError(mathematical.takeError());
    return 8;
  }
  auto bytes = zkc::mathematical::encodeValue(*mathematical);
  if (!bytes) {
    llvm::consumeError(bytes.takeError());
    return 9;
  }
  auto restored = zkc::mathematical::decodeValue(*bytes);
  if (!restored) {
    llvm::consumeError(restored.takeError());
    return 10;
  }
  zkc::mathematical::TypeShape field{
      zkc::mathematical::TypeShape::Kind::Nominal, 0, "field", {}, {}};
  if (auto error =
          zkc::mathematical::checkInstalledDomainType("bls12-381.fr", field)) {
    llvm::consumeError(std::move(error));
    return 11;
  }
  return *mathematical != *restored;
}
