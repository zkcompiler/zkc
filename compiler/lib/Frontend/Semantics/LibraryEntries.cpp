#include "LibraryEntries.h"
#include "zkc/Support/Json.h"
#include <set>

namespace zkc::frontend::semantics {
llvm::Error checkLibraryEntry(const LibraryEntry &entry,
                              const source::Function &formed,
                              llvm::ArrayRef<source::Names> resultPaths,
                              const source::Function &target) {
  const auto &forwarding = entry.forwarding;
  auto failure = [] {
    return zkc::error("source-library-entry-layout",
                      "linked entry and formed source signature disagree");
  };
  if (entry.header.name != formed.name || forwarding.name != formed.name ||
      entry.header.body || entry.header.generic ||
      forwarding.arguments.size() != formed.arguments.size() ||
      target.arguments.size() != formed.arguments.size() ||
      forwarding.results != formed.results ||
      target.results != formed.results ||
      resultPaths != llvm::ArrayRef<source::Names>(entry.resultPaths) ||
      !forwarding.body || forwarding.body->size() != 2)
    return failure();
  source::Names inputs;
  std::set<std::string> values;
  for (size_t i = 0; i < formed.arguments.size(); ++i) {
    const auto &a = formed.arguments[i];
    const auto &b = forwarding.arguments[i];
    if (a.name != b.name || a.type != b.type ||
        a.type != target.arguments[i].type || !values.insert(a.name).second)
      return failure();
    inputs.push_back(a.name);
  }
  const auto &invoke = forwarding.body->front();
  const auto &exit = forwarding.body->back();
  const auto *call = invoke.get<source::AlgorithmCall>();
  const auto *returned = exit.get<source::Return>();
  if (!call || !returned || invoke.site != "invoke" || !exit.site.empty() ||
      call->callee != target.name || !call->staticArguments.empty() ||
      call->inputs != inputs || call->outputs.size() != formed.results.size() ||
      returned->values != call->outputs)
    return failure();
  for (const auto &output : call->outputs)
    if (!values.insert(output).second)
      return failure();
  return llvm::Error::success();
}
} // namespace zkc::frontend::semantics
