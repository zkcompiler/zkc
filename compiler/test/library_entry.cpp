#include "../lib/Frontend/Semantics/LibraryEntries.h"
#include "Names.h"
#include <functional>

using namespace zkc;
using namespace zkc::frontend;

int main() {
  lowering::LibraryEntry entry;
  entry.header.name = "Alias";
  auto &forwarding = entry.forwarding;
  forwarding.name = "Alias";
  forwarding.arguments = {{"pair.first", "bool"}, {"pair.second", "index"}};
  forwarding.results = {"bool", "index"};
  source::Instruction call, ret;
  call.site = "invoke";
  call.value = source::AlgorithmCall{
      "Internal", {"pair.first", "pair.second"}, {"result0", "result1"}, {}};
  ret.value = source::Return{{"result0", "result1"}};
  forwarding.body = source::Body{call, ret};
  entry.resultPaths = {{"first", "second"}};
  source::Function formed = forwarding, target = forwarding;
  formed.body.reset();
  target.name = "Internal";
  target.arguments[0].name = "arg0";
  target.arguments[1].name = "arg1";
  auto check = [&](const lowering::LibraryEntry &candidate) {
    return semantics::checkLibraryEntry(candidate, formed, entry.resultPaths,
                                        target);
  };
  if (auto error = check(entry)) {
    llvm::consumeError(std::move(error));
    return 1;
  }
  // Identical leaf counts do not establish a correspondence: paths, types,
  // target, order and single-use forwarding must all agree independently.
  using Change = std::function<void(lowering::LibraryEntry &)>;
  const Change invalid[] = {
      [](auto &e) { e.forwarding.arguments[0].name = "pair.other"; },
      [](auto &e) { e.forwarding.arguments[0].type = "index"; },
      [](auto &e) { std::swap(e.resultPaths[0][0], e.resultPaths[0][1]); },
      [](auto &e) { e.forwarding.results.pop_back(); },
      [](auto &e) { e.header.body.emplace(); },
      [](auto &e) { e.forwarding.body->front().site = "other"; },
      [](auto &e) { e.forwarding.body->back().site = "return"; },
      [](auto &e) { e.forwarding.body->push_back(e.forwarding.body->back()); },
      [](auto &e) {
        e.forwarding.body->front()
            .template get<source::AlgorithmCall>()
            ->callee = "Other";
      },
      [](auto &e) {
        e.forwarding.body->back().template get<source::Return>()->values[1] =
            "result0";
      },
      [](auto &e) {
        e.forwarding.body->front()
            .template get<source::AlgorithmCall>()
            ->outputs[0] = "pair.first";
        e.forwarding.body->back().template get<source::Return>()->values[0] =
            "pair.first";
      },
  };
  for (const auto &change : invalid) {
    auto candidate = entry;
    change(candidate);
    if (!namesIdentifier(llvm::toString(check(candidate)),
                         "source-library-entry-layout"))
      return 2;
  }
  // Empty aggregate paths agree only with an empty formed result layout.
  auto paths = entry.resultPaths;
  paths[0].clear();
  return !namesIdentifier(llvm::toString(semantics::checkLibraryEntry(
                              entry, formed, paths, target)),
                          "source-library-entry-layout");
}
