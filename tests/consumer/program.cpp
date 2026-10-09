#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
int main() {
  auto json = zkc::parseJson(
      R"(["zkc.program",[],[],[["participant","p","main","P",[["x","bool@native.bool/1"]],["bool@native.bool/1"],[["return",["x"]]],[]]],[["entry","main",[["P","p"]]]]])");
  if (!json) {
    llvm::consumeError(json.takeError());
    return 1;
  }
  auto program = zkc::program::decode(*json);
  if (!program) {
    llvm::consumeError(program.takeError());
    return 2;
  }
  if (auto error = zkc::protocol::admit(*program)) {
    llvm::consumeError(std::move(error));
    return 3;
  }
  return zkc::program::encode(*program) != *json;
}
