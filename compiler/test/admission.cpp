#include "zkc/Protocol/Admission.h"
#include "zkc/Compiler/Instantiation.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cstdlib>

using namespace llvm;
using namespace zkc;

namespace {
source::Module chain(unsigned length, bool reverseNames, bool cycle = false) {
  source::Module module;
  auto name = [&](unsigned i) {
    return "P" + std::to_string(1000 + (reverseNames ? length - i : i));
  };
  for (unsigned i = 0; i < length; ++i) {
    source::Protocol protocol;
    protocol.name = name(i);
    protocol.roles = {"Alice"};
    protocol.body = source::Body{};
    if (i || cycle) {
      auto callee = name(i ? i - 1 : length - 1);
      protocol.dependencies.push_back({{}, "child", callee, {}});
      source::Instruction call;
      call.site = "invoke";
      call.value = source::ProtocolCall{"child", {}, {}};
      protocol.body->push_back(std::move(call));
    }
    source::Instruction result;
    result.value = source::Return{};
    protocol.body->push_back(std::move(result));
    module.protocols.push_back(std::move(protocol));
  }
  return module;
}
void check(const source::Module &module, bool accepted,
           StringRef refusal = "interactive-call-depth") {
  auto error = protocol::admit(module, false);
  if (bool(error) == accepted) {
    errs() << "unexpected admission: " << toString(std::move(error)) << '\n';
    std::exit(1);
  }
  if (error && toString(std::move(error)) != refusal) {
    errs() << "wrong graph refusal\n";
    std::exit(1);
  }
}
void configurations(unsigned length, bool reverseNames, bool cycle = false) {
  source::Module module;
  source::GenericFunction def;
  def.name = "Empty";
  source::Instruction result;
  result.value = source::Return{};
  def.body.push_back(std::move(result));
  module.definitions.push_back(std::move(def));
  auto name = [&](unsigned i) {
    return "C" + std::to_string(1000 + (reverseNames ? length - i : i));
  };
  for (unsigned i = 0; i < length; ++i) {
    source::Configuration config;
    config.name = name(i);
    config.base = i ? name(i - 1) : cycle ? name(length - 1) : "Empty";
    module.configurations.push_back(std::move(config));
  }
  for (unsigned permutation = 0; permutation < 2; ++permutation) {
    auto checked = generic::prepareLibrary(module);
    if (bool(checked) != (length <= 64 && !cycle)) {
      errs() << "configuration depth depends on naming/order\n";
      if (!checked)
        errs() << toString(checked.takeError()) << '\n';
      std::exit(1);
    }
    if (!checked &&
        toString(checked.takeError()) != "generic-configuration-reference")
      std::exit(1);
    std::reverse(module.configurations.begin(), module.configurations.end());
  }
}
} // namespace

int main() {
  // A memoized suffix must contribute its height regardless of spelling or
  // declaration order. The existing depth budget admits at most 65 nodes.
  for (bool reverse : {false, true}) {
    for (unsigned length : {1u, 64u, 65u, 66u, 80u}) {
      auto module = chain(length, reverse);
      check(module, length <= 65);
      std::reverse(module.protocols.begin(), module.protocols.end());
      check(module, length <= 65);
    }
    check(chain(1, reverse, true), false, "interactive-call-cycle");
    check(chain(12, reverse, true), false, "interactive-call-cycle");
  }
  for (bool reverse : {false, true}) {
    for (unsigned length : {1u, 63u, 64u, 65u, 80u})
      configurations(length, reverse);
    configurations(1, reverse, true);
    configurations(12, reverse, true);
  }
  outs()
      << "call-graph bounds are independent of naming and declaration order\n";
}
