#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
int main() {
  auto input = llvm::MemoryBuffer::getSTDIN();
  if (!input)
    return 2;
  auto json = zkc::parseJson((*input)->getBuffer());
  if (!json) {
    llvm::errs() << llvm::toString(json.takeError());
    return 1;
  }
  auto program = zkc::program::decode(*json);
  if (!program) {
    llvm::errs() << llvm::toString(program.takeError());
    return 1;
  }
  if (auto error = zkc::protocol::admit(*program)) {
    llvm::errs() << llvm::toString(std::move(error));
    return 1;
  }
  llvm::outs() << zkc::printJson(zkc::program::encode(*program));
}
