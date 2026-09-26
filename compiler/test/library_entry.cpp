#include "../lib/Frontend/Semantics/LibraryEntries.h"
#include "Names.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>

using namespace zkc;
using namespace zkc::frontend;

int main() {
  LibraryEntry entry;
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
  auto check = [&](const LibraryEntry &candidate) {
    return semantics::checkLibraryEntry(candidate, formed, entry.resultPaths,
                                        target);
  };
  if (auto error = check(entry)) {
    llvm::consumeError(std::move(error));
    return 1;
  }
  // Identical leaf counts do not establish a correspondence: paths, types,
  // target, order and single-use forwarding must all agree independently.
  using Change = std::function<void(LibraryEntry &)>;
  const std::pair<llvm::StringRef, Change> invalid[] = {
      {"argument path",
       [](auto &e) { e.forwarding.arguments[0].name = "pair.other"; }},
      {"argument type",
       [](auto &e) { e.forwarding.arguments[0].type = "index"; }},
      {"result paths",
       [](auto &e) { std::swap(e.resultPaths[0][0], e.resultPaths[0][1]); }},
      {"result arity", [](auto &e) { e.forwarding.results.pop_back(); }},
      {"authored body", [](auto &e) { e.header.body.emplace(); }},
      {"invoke site",
       [](auto &e) { e.forwarding.body->front().site = "other"; }},
      {"return site",
       [](auto &e) { e.forwarding.body->back().site = "return"; }},
      {"extra instruction",
       [](auto &e) {
         e.forwarding.body->push_back(e.forwarding.body->back());
       }},
      {"wrong target",
       [](auto &e) {
         e.forwarding.body->front()
             .template get<source::AlgorithmCall>()
             ->callee = "Other";
       }},
      {"input order",
       [](auto &e) {
         auto &inputs = e.forwarding.body->front()
                            .template get<source::AlgorithmCall>()
                            ->inputs;
         std::swap(inputs[0], inputs[1]);
       }},
      {"static arguments",
       [](auto &e) {
         e.forwarding.body->front()
             .template get<source::AlgorithmCall>()
             ->staticArguments.push_back("koala-bear");
       }},
      {"repeated return",
       [](auto &e) {
         e.forwarding.body->back().template get<source::Return>()->values[1] =
             "result0";
       }},
      {"shadowed output",
       [](auto &e) {
         e.forwarding.body->front()
             .template get<source::AlgorithmCall>()
             ->outputs[0] = "pair.first";
         e.forwarding.body->back().template get<source::Return>()->values[0] =
             "pair.first";
       }},
  };
  unsigned failures = 0;
  auto rejects = [&](llvm::StringRef name, llvm::Error result) {
    if (!namesIdentifier(llvm::toString(std::move(result)),
                         "source-library-entry-layout")) {
      llvm::errs() << name << ": expected source-library-entry-layout\n";
      ++failures;
    }
  };
  for (const auto &[name, change] : invalid) {
    auto candidate = entry;
    change(candidate);
    rejects(name, check(candidate));
  }
  auto different = target;
  different.arguments[0].type = "index";
  rejects("target input type",
          semantics::checkLibraryEntry(entry, formed, entry.resultPaths,
                                       different));
  different = target;
  different.results[0] = "index";
  rejects("target result type",
          semantics::checkLibraryEntry(entry, formed, entry.resultPaths,
                                       different));
  different = target;
  different.name = "Other";
  rejects("same signature, different expected entry",
          semantics::checkLibraryEntry(entry, formed, entry.resultPaths,
                                       different));
  // Empty aggregate paths agree only with an empty formed result layout.
  auto paths = entry.resultPaths;
  paths[0].clear();
  rejects("empty result paths",
          semantics::checkLibraryEntry(entry, formed, paths, target));
  return failures ? 1 : 0;
}
