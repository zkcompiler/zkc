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
  return llvm::toString(std::move(rejected)) != "relation-generated-function";
}
