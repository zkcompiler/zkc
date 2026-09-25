#include "zkc/Relation/Matrices.h"
#include "zkc/Support/Json.h"

int main() {
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
