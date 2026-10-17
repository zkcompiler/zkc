#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/IRMapping.h"
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
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
local::FuncOp calculation(ModuleOp module) {
  return SymbolTable(unit(module)).lookup<local::FuncOp>("calculation");
}
void outlineTotal(ModuleOp module) {
  auto total = SymbolTable(unit(module)).lookup<func::FuncOp>("total");
  require(bool(total), "missing total helper");
  OpBuilder builder(total);
  auto function = local::FuncOp::create(builder, total.getLoc(), "calculation",
                                        total.getFunctionType());
  function->setAttr("logical_origin",
                    builder.getArrayAttr({builder.getStringAttr("calculation"),
                                          builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(function.addEntryBlock());
  IRMapping mapping;
  mapping.map(total.getArguments(), function.getArguments());
  unsigned ordinal = 0;
  for (auto &operation : total.front().without_terminator()) {
    auto *copy = builder.clone(operation, mapping);
    copy->setAttr("site", builder.getStringAttr("calculation_" +
                                                std::to_string(ordinal++)));
  }
  SmallVector<Value> outputs;
  for (auto value : total.front().back().getOperands())
    outputs.push_back(mapping.lookup(value));
  local::ReturnOp::create(builder, total.getLoc(), outputs);
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
          outlineTotal(*source);
          auto original = copy(*source), ordered = copy(*source),
               bulk = copy(*source);
          mathematical::RealizationWork work, orderedWork;
          require(succeeded(mathematical::lowerCalculations(
                      unit(*bulk), {calculation(*bulk)})),
                  "ordinary bulk path refused");
          require(succeeded(mathematical::lowerCalculations(
                      unit(*ordered), {calculation(*ordered)}, {false, false},
                      &orderedWork)),
                  "ordered total path refused");
          require(!same(*bulk, *ordered),
                  "fixture did not select optional bulk work");
          unsigned diagnostics = 0;
          ScopedDiagnosticHandler record(&context, [&](Diagnostic &) {
            ++diagnostics;
            return success();
          });
          require(succeeded(mathematical::lowerCalculations(
                      unit(*source), {calculation(*source)}, {}, &work,
                      {100000, 1})),
                  "optional total comparison exhaustion refused");
          require(
              !diagnostics && same(*source, *ordered) &&
                  succeeded(verify(*source)),
              "retry diagnosed a discarded proposal or changed ordered output");
          require(succeeded(mathematical::verifyCalculationRecipes(
                      unit(*original), unit(*source), {calculation(*source)})),
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
    outlineTotal(*source);
    auto original = copy(*source);
    std::string diagnostics;
    ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
      diagnostics += diagnostic.str();
      return success();
    });
    require(failed(mathematical::lowerCalculations(unit(*source),
                                                   {calculation(*source)}, {},
                                                   nullptr, {0, 100000})) &&
                same(*source, *original),
            "required capacity published a partial total body");
    require(diagnostics.find("finite-verification-capacity") !=
                std::string::npos,
            "required capacity lost its diagnostic");
  });
  return cases.result();
}
