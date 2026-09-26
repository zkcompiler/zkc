#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Table.h"

int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  zkc::registerTableLibrary(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto source = zkc::parseJson(R"(["zkc-request",1,"finite-source-1",
    ["trace",[["x",["scalar","f7"],["shared"],"argument"]],
      ["scalar","f7"],[["table-protocol","1"]]],[],["return",0]])");
  if (!source) {
    llvm::consumeError(source.takeError());
    return 1;
  }
  auto module = zkc::importSource(*source, context);
  if (!module) {
    llvm::consumeError(module.takeError());
    return 2;
  }
  mlir::PassManager pipeline(&context);
  pipeline.addPass(zkc::createLowerPIRToPlanPass());
  pipeline.addPass(zkc::createLowerPlanToPhysicalPass("materialized"));
  if (failed(pipeline.run(module->get())) ||
      failed(mlir::verify(module->get())))
    return 3;
  auto exported = zkc::exportPlan(module->get());
  if (!exported) {
    llvm::consumeError(exported.takeError());
    return 4;
  }
  // Factory use must not pull in application pipeline registration.
  return mlir::PassInfo::lookup("lower-pir-to-plan") ? 5 : 0;
}
