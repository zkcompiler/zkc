#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Support/Json.h"

int main() {
  // An explicit resolver supplies relation bytes; no MLIR or compiler driver
  // participates in capture, decoding, source checking or common admission.
  zkc::relation::Constraint row{{{{2, "1"}}, {{3, "1"}}, {{1, "1"}}}};
  auto relation = zkc::relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row});
  if (!relation) {
    llvm::consumeError(relation.takeError());
    return 1;
  }
  auto result = zkc::frontend::loadProtocolDocument(
      "module { relation Circuit = r1cs(\"circuit.json\"); }", "root.pir",
      [&](llvm::StringRef path, size_t) -> llvm::Expected<std::string> {
        if (path != "circuit.json")
          return zkc::error("unexpected-path");
        return zkc::printJson(relation->encode());
      });
  if (!result) {
    llvm::consumeError(result.takeError());
    return 2;
  }
  unsigned reads = 0;
  auto rejected = zkc::frontend::loadProtocolDocument(
      "module { relation R = r1cs(\"../escape.r1cs\"); }", "root.pir",
      [&](llvm::StringRef, size_t) -> llvm::Expected<std::string> {
        ++reads;
        return zkc::error("unexpected-read");
      });
  if (rejected)
    return 3;
  auto error = llvm::toString(rejected.takeError());
  return reads != 0 || error != "relation-asset-path";
}
