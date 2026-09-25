#include "zkc/Source/Execution.h"
#include "zkc/Frontend/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
namespace {
void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
} // namespace
int main() {
  auto document = take(frontend::parseProtocolDocument(R"pir(module {
    bind one = field.constant(koala-bear);
    bind add = field.add(koala-bear);
    bind equal = field.equal(koala-bear);
    bind require = control.require();
    fn Increment(x: koala-bear::Element) -> (koala-bear::Element) {
      let unit = one() attributes ("1");
      let next = add(x, unit);
      return (next);
    }
    fn Check(x: koala-bear::Element) -> () {
      let ok = equal(x, x);
      require(ok);
      return ();
    }
    protocol Exchange {
      roles (P, V);
      inputs (P initial: koala-bear::Element);
      outputs (P koala-bear::Element);
      loop [rounds] 12 carry (x = initial) -> (last) {
        local P: let next = Increment(x);
        message value: P(next) -> V(received);
        local V: Check(received);
        yield (next);
      }
      return (last);
    }
    instance exchange: Exchange { roles (P = Prover, V = Verifier); }
    entry main = exchange;
  })pir"));
  auto view = take(source::inspectExecution(*document.module(), "main"));
  require(view.values.at("v0").role == "Prover", "input owner lost");
  require(view.order.size() == 60, "wrong expanded operation count");
  size_t messages = 0, guards = 0;
  for (size_t i = 0; i < view.order.size(); ++i) {
    const auto &op = view.operations.at(view.order[i]);
    require(op.ordinal == i, "operation order lost");
    if (op.callee == "field.constant") {
      require(op.role == "Prover" && op.attributes == source::Names{"1"},
              "local metadata lost");
    }
    if (op.callee == "message") {
      ++messages;
      require(op.role == "Prover" && op.receiver == "Verifier",
              "message participants lost");
      require(op.inputs != op.outputs, "received value equated to sent value");
      require(view.values.at(op.inputs[0]).role == "Prover",
              "sender value owner lost");
      require(view.values.at(op.outputs[0]).role == "Verifier",
              "receiver value owner lost");
    }
    if (op.callee == "control.require") {
      ++guards;
      require(op.role == "Verifier", "guard role lost");
      require(view.guards.at(view.order[i]).value == op.inputs[0],
              "guard input changed");
    }
  }
  require(messages == 12 && guards == 12, "query occurrences lost");
  require(view.operations.at("$/0/i2/0/0").ordinal <
              view.operations.at("$/0/i10/0/0").ordinal,
          "lexical paths substituted for temporal order");
  // Programmatic construction retains a reusable algorithm call; source
  // analysis must follow it without losing operation order, roles or guards.
  auto composed = *document.module();
  auto wrapper = composed.functions.front();
  require(wrapper.name == "Increment", "fixture local order");
  wrapper.name = "Wrapper";
  wrapper.origin = source::LogicalOrigin{"Wrapper", {}};
  source::Names arguments;
  for (const auto &argument : wrapper.arguments)
    arguments.push_back(argument.name);
  wrapper.body = source::Body{
      {{}, "inside", source::AlgorithmCall{"Increment", arguments, {"out"}}},
      {{}, "", source::Return{{"out"}}}};
  composed.functions.push_back(std::move(wrapper));
  for (auto &protocol : composed.protocols)
    if (protocol.body)
      source::walk(*protocol.body, [](source::Instruction &instruction) {
        if (auto *call = instruction.get<source::LocalCall>())
          if (call->callee == "Increment")
            call->callee = "Wrapper";
      });
  auto nested = take(source::inspectExecution(composed, "main"));
  require(nested.order.size() == view.order.size(), "nested operations lost");
  for (size_t i = 0; i < view.order.size(); ++i) {
    const auto &before = view.operations.at(view.order[i]);
    const auto &after = nested.operations.at(nested.order[i]);
    require(before.callee == after.callee && before.role == after.role &&
                before.inputs == after.inputs &&
                before.outputs == after.outputs,
            "algorithm analysis changed dataflow");
  }
  require(nested.invocations.size() == view.invocations.size() + 12,
          "nested invocation origins lost");
  auto missing = source::inspectExecution(*document.module(), "absent");
  require(!missing, "missing entry accepted");
  require(toString(missing.takeError()) == "execution-entry",
          "missing entry diagnostic");
}
