#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Project.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
int main() {
  auto commitment =
      zkc::language::domainType("Commitment", "multilinear.kzg.bls12-381/1");
  auto field = zkc::language::domainMember(commitment, "ValueField");
  if (!field) {
    llvm::errs() << llvm::toString(field.takeError());
    return 8;
  }
  if (*field != zkc::language::domainType("Field", "bls12-381.fr") ||
      !zkc::language::isStaticOnly(commitment) ||
      zkc::language::isStaticOnly(*field))
    return 9;

  auto relation = zkc::relation::R1CS::create("bls12-381.fr", 2, 0, 1, {});
  if (!relation) {
    llvm::errs() << llvm::toString(relation.takeError());
    return 6;
  }
  auto capture = zkc::language::capture(
      {{"m", R"(module m;
    struct Pair<T:Type>{pub first:T,pub second:T}
    fn swap<T:Type+Copy+Drop>(x:Pair<T>)->Pair<T>{
      return Pair<T>{first:x.second,second:x.first};
    }
    protocol Run roles(P)(x:Pair<bool>@P)->(r:Pair<bool>@P){
      local P let r=swap(x);return(r=r);
    }
    entry Demo=Run;)",
        "consumer.zkc"}},
      {{"circuit", "r1cs-json", zkc::printJson(relation->encode()),
        "unused.json"}},
      {});
  if (!capture) {
    llvm::errs() << llvm::toString(capture.takeError());
    return 1;
  }
  auto checked = zkc::language::analyze(*capture).checkedProject();
  if (!checked) {
    llvm::errs() << llvm::toString(checked.takeError());
    return 2;
  }
  if (checked->assets().size() != 1 ||
      checked->assets()[0].identity() != relation->identity())
    return 7;
  auto entry = zkc::language::closeEntry(*checked, "m::Demo");
  if (!entry) {
    llvm::errs() << llvm::toString(entry.takeError());
    return 3;
  }
  zkc::language::Layouts layouts(*checked);
  auto layout = layouts.get(entry->protocol().inputs.front().type);
  if (!layout) {
    llvm::errs() << llvm::toString(layout.takeError());
    return 4;
  }
  return (*layout)->fields.size() == 2 && (*layout)->leaves.size() == 2 &&
                 entry->protocol().symbol == "s1_m3_Run"
             ? 0
             : 5;
}
