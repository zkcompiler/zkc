#include "zkc/Relation/Bundle.h"
#include "zkc/Relation/Matrices.h"
#include "zkc/Support/Json.h"

int main() {
  auto bundle = zkc::relation::readBundleText(R"(["zkc.relation-bundle/0",[],[],
    [["optional","optional",["fixed",3],"finite",
      [["config","config","koala-bear",2]],
      ["zkc.ring/0",[],[],[]],[],[],[]]]])");
  if (!bundle) {
    llvm::consumeError(bundle.takeError());
    return 1;
  }
  auto widths = zkc::relation::bundleTableWidths(*bundle, 0, "koala-bear");
  if (!widths) {
    llvm::consumeError(widths.takeError());
    return 1;
  }
  if (widths->witnessWidth != 0 || widths->configWidth != 2 ||
      widths->publicWidth != 0)
    return 1;
  zkc::relation::Constraint row{{{{2, "1"}}, {{3, "1"}}, {{1, "1"}}}};
  auto relation = zkc::relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row});
  if (!relation) {
    llvm::consumeError(relation.takeError());
    return 1;
  }
  auto values = zkc::relation::matrixValues(*relation);
  return zkc::printJson((*values.getAsArray())[0]) !=
             "[\"2\",\"4\",[[\"0\",\"2\",\"1\"]]]" ||
         zkc::relation::matrixIdentity(*relation, 0).size() != 64;
}
