#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Target/CpuTarget.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"
#include <functional>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string print(OpPassManager &pipeline) {
  std::string text;
  llvm::raw_string_ostream stream(text);
  pipeline.printAsTextualPipeline(stream);
  return text;
}
unsigned calls(ModuleOp module, llvm::StringRef contract) {
  unsigned count = 0;
  module.walk([&](exec::ApplyOp call) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        call, call.getBindingAttr());
    count += binding && binding.getContract() == contract;
  });
  return count;
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "expected finite mathematical fixture");
  auto bytes = llvm::MemoryBuffer::getFile(argv[1]);
  require(bool(bytes), "fixture reading");
  Cases cases;
  using Factory =
      std::function<std::unique_ptr<Pass>(MathematicalSelectionPolicy)>;
  const Factory factories[] = {
      [](auto p) { return protocol::createPrepareProtocolPass(false, p); },
      [](auto p) { return protocol::createProjectProtocolPass(false, p); },
      [](auto p) { return protocol::createLowerMathPass(p); },
      [](auto p) { return protocol::createLowerClosedParticipantPass(p); },
      [](auto p) { return computation::createRealizeComputationsPass(p); },
      [](auto p) {
        return protocol::createSelectPhysicalPass({}, false, false, nullptr, {},
                                                  p);
      }};
  for (auto factory : factories) {
    registerPass([factory] { return factory({}); });
    auto name = factory({})->getArgument().str();
    cases.run(name + " options survive pipeline copying and parsing", [&] {
      MathematicalSelectionPolicy policy{false, true, true, false,
                                         NumericalExpressionMode::VectorOnly};
      OpPassManager original("builtin.module");
      original.addPass(factory(policy));
      auto text = print(original);
      for (llvm::StringRef option :
           {"optimize-finite=false", "fuse-vector-reductions=true",
            "fuse-collect-fold=true", "calculation-batching=false",
            "numerical-expressions=vector-only"})
        require(llvm::StringRef(text).contains(option),
                "lost policy field " + option);
      OpPassManager copy(original);
      require(print(copy) == text, "pass cloning changed its policy");
      auto parsed = parsePassPipeline(text);
      require(succeeded(parsed) && print(*parsed) == text,
              "textual pipeline changed its policy");
    });
    cases.run(name + " refuses unknown numerical mode", [&] {
      std::string error;
      require(failed(factory({})->initializeOptions(
                  "numerical-expressions=unknown",
                  [&](const llvm::Twine &message) {
                    error += message.str();
                    return failure();
                  })),
              "unknown option value accepted");
    });
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  for (bool explicitRealization : {false, true})
    for (bool vectorOnly : {false, true})
      for (bool available : {false, true})
        cases.run(
            llvm::Twine("cloned execution pipeline explicit=") +
                llvm::Twine(explicitRealization) +
                " vector=" + llvm::Twine(vectorOnly) +
                " available=" + llvm::Twine(available),
            [&] {
              auto source =
                  parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
              require(bool(source), "source parsing");
              MathematicalSelectionPolicy policy;
              policy.numericalExpressions =
                  vectorOnly ? NumericalExpressionMode::VectorOnly
                             : NumericalExpressionMode::PreferNative;
              OpPassManager original("builtin.module");
              original.addPass(
                  protocol::createProjectProtocolPass(false, policy));
              original.addPass(protocol::createLowerMathPass(policy));
              if (explicitRealization)
                original.addPass(
                    computation::createRealizeComputationsPass(policy));
              auto cpuTarget = take(target::CpuTarget::parse(
                  available
                      ? R"({"format":"zkc.cpu-target/0","providers":["arkworks"]})"
                      : R"({"format":"zkc.cpu-target/0","providers":[]})"));
              original.addPass(protocol::createSelectPhysicalPass(
                  {}, false, false, nullptr, {}, policy, cpuTarget));
              PassManager copied(&context);
              static_cast<OpPassManager &>(copied) = original;
              std::string diagnostic;
              ScopedDiagnosticHandler handler(&context, [&](Diagnostic &item) {
                diagnostic += item.str();
                return success();
              });
              auto outcome = copied.run(*source);
              if (!available) {
                require(
                    failed(outcome) &&
                        namesIdentifier(diagnostic, "cpu-target-unavailable"),
                    "copied pipeline lost its target restriction: " +
                        diagnostic);
                return;
              }
              require(succeeded(outcome),
                      "copied pipeline failed: " + diagnostic);
              require(
                  vectorOnly ? calls(*source, "vector.mul") &&
                                   !calls(*source, "numerical.map")
                             : calls(*source, "numerical.map") &&
                                   !calls(*source, "vector.mul"),
                  "executed representation differs from the requested policy");
            });
  return cases.result();
}
