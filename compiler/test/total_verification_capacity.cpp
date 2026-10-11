#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string fixture() {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) +
                      "/realized-total.mlir");
  require(bool(input), "missing total fixture");
  std::ostringstream bytes;
  bytes << input.rdbuf();
  return bytes.str();
}
OwningOpRef<ModuleOp> copy(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(ModuleOp a, ModuleOp b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool nested : {false, true}) {
    cases.run(
        nested ? "nested total finite comparison retries ordered"
               : "total finite comparison retries ordered",
        [&] {
          auto text = fixture();
          if (!nested) {
            auto pos = text.find("step=@outside");
            require(pos != std::string::npos, "missing outer step");
            text.replace(pos, std::string("step=@outside").size(),
                         "step=@inside");
          }
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source) && succeeded(verify(*source)),
                  "total source refused");
          auto original = copy(*source), ordered = copy(*source),
               bulk = copy(*source);
          mathematical::RealizationWork work, orderedWork;
          require(succeeded(mathematical::expandMathRealizations(*bulk)),
                  "ordinary bulk path refused");
          require(succeeded(mathematical::expandMathRealizations(
                      *ordered, {false, false}, &orderedWork)),
                  "ordered total path refused");
          require(!same(*bulk, *ordered),
                  "fixture did not select optional bulk work");
          unsigned diagnostics = 0;
          ScopedDiagnosticHandler record(&context, [&](Diagnostic &) {
            ++diagnostics;
            return success();
          });
          require(succeeded(mathematical::expandMathRealizations(
                      *source, {}, &work, {100000, 1})),
                  "optional total comparison exhaustion refused");
          require(
              !diagnostics && same(*source, *ordered) &&
                  succeeded(verify(*source)),
              "retry diagnosed a discarded proposal or changed ordered output");
          require(succeeded(mathematical::verifyMathRealizationsPreserved(
                      *original, *source)),
                  "fallback lost original helper correspondence");
          require(work.helperOperations == orderedWork.helperOperations &&
                      work.helperSlots == orderedWork.helperSlots,
                  "optional attempt consumed required fallback reserve");
          require(work.matching.structural < orderedWork.matching.structural,
                  "discarded optional recognition work was replenished");
        });
  }
  cases.run("required total reader exhaustion refuses atomically", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "total source refused");
    auto original = copy(*source);
    std::string diagnostics;
    ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
      diagnostics += diagnostic.str();
      return success();
    });
    require(failed(mathematical::expandMathRealizations(*source, {}, nullptr,
                                                        {0, 100000})) &&
                same(*source, *original),
            "required capacity published a partial total body");
    require(diagnostics.find("finite-verification-capacity") !=
                std::string::npos,
            "required capacity lost its diagnostic");
  });
  return cases.result();
}
