#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"

int main() {
  // Owned input and immutable queries survive the input's lifetime. This
  // consumer links only Frontend: neither MLIR nor file loading is required.
  auto analysis =
      zkc::frontend::analyzeProtocol(zkc::frontend::Input::withoutFile(
          "module { fn Id(x: bool) -> bool { return x; } }"));
  if (!analysis.complete())
    return 1;
  auto first = analysis.lower();
  auto second = analysis.lower();
  if (!first || !second) {
    if (!first)
      llvm::consumeError(first.takeError());
    if (!second)
      llvm::consumeError(second.takeError());
    return 2;
  }
  auto &module = std::get<zkc::source::Module>(*first);
  if (zkc::source::encode(module) !=
      zkc::source::encode(std::get<zkc::source::Module>(*second)))
    return 3;
  if (auto error = zkc::protocol::admit(module, false)) {
    llvm::consumeError(std::move(error));
    return 4;
  }
  // Returning common content must not expose mutable snapshot storage. The
  // checked handle also owns its result after the analysis handle is replaced.
  auto checked = analysis.checkedModule();
  if (!checked) {
    llvm::consumeError(checked.takeError());
    return 5;
  }
  module.functions.clear();
  analysis = zkc::frontend::analyzeProtocol(
      zkc::frontend::Input::withoutFile("module {}"));
  auto retained = zkc::frontend::lower(*checked);
  if (!retained) {
    llvm::consumeError(retained.takeError());
    return 6;
  }
  if (zkc::source::encode(std::get<zkc::source::Module>(*retained)) !=
      zkc::source::encode(std::get<zkc::source::Module>(*second)))
    return 7;
  auto invalid =
      zkc::frontend::analyzeProtocol(zkc::frontend::Input::withoutFile(
          "module { fn Bad(x: bool) -> bool { return missing; } }"));
  auto rejected = invalid.lower();
  if (rejected)
    return 8;
  llvm::consumeError(rejected.takeError());
  return invalid.complete() || invalid.diagnostics().empty();
}
