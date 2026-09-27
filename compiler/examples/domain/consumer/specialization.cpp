#include "envelope/Specialization.h"
#include "envelope/Envelope.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace mlir;

namespace {
void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}

constexpr StringLiteral functionSource = R"(module {
  bind first_add = field.add(koala-bear);
  bind second_add = field.add(koala-bear);
  bind unused_mul = field.mul(koala-bear);
  fn SumThree(x: koala-bear::Element, y: koala-bear::Element,
              z: koala-bear::Element) -> koala-bear::Element {
    [first] let partial = first_add(x, y);
    [second] let result = second_add(partial, z);
    return result;
  }
})";

// Authored independently of the frontend result and transformation output.
// In particular, the unused declaration and the two distinct binding/site
// identities are part of the expected source, not synthesized from a baseline.
zkc::source::Module expectedFunction() {
  using namespace zkc::source;
  Module module;
  module.bindings = {{{}, "first_add", {"field.add", {"koala-bear"}, ""}},
                     {{}, "second_add", {"field.add", {"koala-bear"}, ""}},
                     {{}, "unused_mul", {"field.mul", {"koala-bear"}, ""}}};
  Function function;
  function.name = "SumThree";
  function.origin = LogicalOrigin{"SumThree", {}};
  function.arguments = {{"x", "field:koala-bear"},
                        {"y", "field:koala-bear"},
                        {"z", "field:koala-bear"}};
  function.results = {"field:koala-bear"};
  function.body = Body{
      {{},
       "first",
       zkc::source::Operation{"first_add", {}, {}, {"x", "y"}, {"partial"}}},
      {{},
       "second",
       zkc::source::Operation{
           "second_add", {}, {}, {"partial", "z"}, {"result"}}},
      {{}, "", Return{{"result"}}}};
  module.functions.push_back(std::move(function));
  return module;
}

constexpr StringLiteral participantSource = R"(module {
  bind first_add = field.add(koala-bear);
  bind second_add = field.add(koala-bear);
  bind unused_mul = field.mul(koala-bear);
  fn SumThree(x: koala-bear::Element, y: koala-bear::Element,
              z: koala-bear::Element) -> koala-bear::Element {
    [first] let partial = first_add(x, y);
    [second] let result = second_add(partial, z);
    return result;
  }
  protocol SendSum {
    roles(P, V);
    inputs(P x: koala-bear::Element, P y: koala-bear::Element,
           P z: koala-bear::Element);
    outputs(V koala-bear::Element);
    local P: let total = SumThree(x, y, z);
    message sum: P(total) -> V(received);
    return received;
  }
  instance run: SendSum { roles(P = prover, V = verifier); }
  entry main = run;
})";

zkc::Compilation compile(StringRef text, zkc::ProtocolAction action) {
  DialectRegistry registry;
  registry.insert<envelope::EnvelopeDialect>();
  return take(zkc::compileProtocol(
      take(zkc::frontend::parseProtocolDocument(text, "specialization.pir")),
      {action, {}}, registry));
}

std::string snapshot(ModuleOp module) {
  std::string text;
  raw_string_ostream stream(text);
  module.print(stream, OpPrintingFlags().enableDebugInfo());
  return text;
}

SmallVector<zkc::FieldSumOp> sums(ModuleOp module) {
  SmallVector<zkc::FieldSumOp> result;
  module.walk([&](zkc::FieldSumOp op) { result.push_back(op); });
  return result;
}

size_t composites(ModuleOp module) {
  size_t count = 0;
  module.walk([&](envelope::FieldSumChainOp) { ++count; });
  return count;
}

void roundtrip(ModuleOp module) {
  auto before = snapshot(module);
  auto source = take(zkc::protocol::exportModule(module));
  auto original = sums(module);
  require(original.size() == 2, "fixture must contain exactly two additions");
  require(succeeded(envelope::specializeFieldSums(module)),
          "specialization failed");
  require(composites(module) == 1 && sums(module).empty(),
          "specialization did not replace two additions with one composite");
  {
    ScopedDiagnosticHandler silence(module.getContext(), [](Diagnostic &) {});
    auto premature = zkc::protocol::exportModule(module);
    require(!premature, "executable export accepted an unlowered composite");
    auto reason = toString(premature.takeError());
    require(reason == "interactive-unknown-attribute",
            "unlowered composite refused for an unrelated reason: " + reason);
  }
  require(succeeded(envelope::decomposeFieldSums(module)),
          "full decomposition failed");
  require(composites(module) == 0, "full conversion left a composite");
  require(succeeded(verify(module)), "restored module failed verification");
  require(snapshot(module) == before,
          "decomposition changed native IR, metadata, order or locations");
  require(take(zkc::protocol::exportModule(module)) == source,
          "decomposition changed the canonical carrier");
}

void negativePatterns() {
  // These malformed/unmatched roots are deliberately tested below the helper's
  // admission gate, using the public ordinary MLIR pattern population API.
  for (unsigned mutation = 0; mutation != 5; ++mutation) {
    auto input = compile(functionSource, zkc::ProtocolAction::Import);
    ModuleOp module = input.module();
    auto pair = sums(module);
    require(pair.size() == 2, "negative fixture shape");
    if (mutation == 0)
      pair[1]->removeAttr("binding");
    else if (mutation == 1)
      pair[1]->setAttr("parameters",
                       StringAttr::get(module.getContext(), "bad"));
    else if (mutation == 2)
      pair[1]->setOperand(1, pair[0]->getResult(0)); // two uses
    else if (mutation == 3)
      pair[1]->setOperands({pair[1]->getOperand(1), pair[1]->getOperand(0)});
    else
      pair[1]->setOperands(ValueRange{pair[1]->getOperand(0)});
    auto before = snapshot(module);
    RewritePatternSet patterns(module.getContext());
    envelope::populateFieldSumSpecializationPatterns(patterns);
    PatternRewriter rewriter(module.getContext());
    for (const auto &pattern : patterns.getNativePatterns())
      require(failed(pattern->matchAndRewrite(pair[1], rewriter)),
              "malformed or out-of-scope pair unexpectedly matched");
    require(snapshot(module) == before, "failed match mutated the input");
  }
  auto input = compile(functionSource, zkc::ProtocolAction::Import);
  auto module = input.module();
  require(succeeded(envelope::specializeFieldSums(module)), "negative setup");
  module.walk([&](envelope::FieldSumChainOp op) {
    op->setAttr("first_attributes", DictionaryAttr::get(module.getContext()));
  });
  ScopedDiagnosticHandler silence(module.getContext(), [](Diagnostic &) {});
  require(failed(envelope::decomposeFieldSums(module)),
          "full conversion accepted missing restoration metadata");
  require(composites(module) == 1, "failed conversion erased the illegal op");
}
} // namespace

int main(int argc, char **argv) {
  require(argc <= 2, "usage: envelope-specialization [restored-physical.json]");
  auto function = compile(functionSource, zkc::ProtocolAction::Import);
  auto expected = take(zkc::protocol::importModule(
      expectedFunction(), *function.module().getContext()));
  require(take(zkc::protocol::exportModule(function.module())) ==
              take(zkc::protocol::exportModule(*expected)),
          "authored source differs from independently authored expected IR");
  auto pair = sums(function.module());
  require(pair.size() == 2 && pair[0]->getNumOperands() == 2 &&
              pair[1]->getNumOperands() == 2 &&
              pair[1]->getOperand(0) == pair[0]->getResult(0) &&
              pair[0]->getAttrOfType<FlatSymbolRefAttr>("binding").getValue() ==
                  "first_add" &&
              pair[1]->getAttrOfType<FlatSymbolRefAttr>("binding").getValue() ==
                  "second_add",
          "independent native two-add graph expectation failed");
  roundtrip(function.module());
  negativePatterns();

  auto common = compile(participantSource, zkc::ProtocolAction::Expand);
  roundtrip(common.module());
  auto restoredCommon = take(zkc::protocol::exportModule(common.module()));
  auto projected = take(zkc::protocol::project(common.module()));
  roundtrip(*projected);
  require(succeeded(zkc::protocol::lowerPhysical(*projected)),
          "restored participant physical selection failed");
  auto restored = take(zkc::protocol::exportModule(*projected));
  auto baseline = compile(participantSource, zkc::ProtocolAction::Plan);
  require(restored == take(zkc::protocol::exportModule(baseline.module())),
          "restored physical carrier differs from direct compilation");
  auto content = take(zkc::protocol::exportSource(*projected));
  const auto &participants = std::get<zkc::source::Participants>(content);
  require(participants.bindings.size() == 3,
          "physical lowering removed a retained binding declaration");
  if (argc == 2) {
    auto write = [](StringRef path, const json::Value &value) {
      std::error_code error;
      raw_fd_ostream output(path, error, sys::fs::OF_Text);
      require(!error, "cannot open artifact output");
      output << value << '\n';
      output.flush();
      require(!output.has_error(), "cannot write artifact output");
    };
    write(argv[1], restored);
    // Supply both independent readers with the admitted common source paired
    // with the restored physical participant carrier.
    write(std::string(argv[1]) + ".source.json", restoredCommon);
  }
  outs() << "two-add specialization: independent source/native expectations, "
            "exact common/logical/physical carrier restoration, pre-lowering "
            "export refusal and malformed-pattern controls passed\n";
}
