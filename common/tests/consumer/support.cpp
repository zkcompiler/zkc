#include "zkc/Support/Json.h"

int main() {
  auto value = zkc::parseJson("[123456789012345678901234567890]");
  if (!value) {
    llvm::consumeError(value.takeError());
    return 1;
  }
  return zkc::printJson(*value) != "[123456789012345678901234567890]";
}
