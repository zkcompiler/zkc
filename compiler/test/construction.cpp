// Compare the public construction workflow with the CLI on the same captured
// project. selector_ownership.py supplies the source, descriptor and libraries.
#include "zkc/Compiler/Compilation.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
namespace {
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
frontend::Input read(StringRef path) {
  auto buffer = MemoryBuffer::getFile(path);
  if (!buffer) {
    errs() << path << ": " << buffer.getError().message() << '\n';
    std::exit(1);
  }
  return {(*buffer)->getBuffer().str(), path.str()};
}
} // namespace

int main(int argc, char **argv) {
  if (argc < 3) {
    errs() << "expected source, descriptor, and optional library roots\n";
    return 1;
  }
  std::vector<frontend::Input> libraries;
  for (int i = 3; i < argc; ++i)
    libraries.push_back(read(argv[i]));
  auto project = take(frontend::captureProject(read(argv[1]), libraries));
  auto analysis = frontend::analyzeProject(std::move(project));
  auto input = read(argv[2]);
  auto descriptor =
      take(frontend::parseProtocolDocument(input.text(), input.filename()));
  if (!descriptor.construction()) {
    errs() << "expected a construction descriptor\n";
    return 1;
  }
  mlir::DialectRegistry registry;
  auto result =
      take(constructProtocol(analysis, *descriptor.construction(), registry));
  outs() << printJson(result.certificate) << '\n';
}
