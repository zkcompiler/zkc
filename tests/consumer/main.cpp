#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/Registry.h"
int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  if (mlir::PassInfo::lookup("zkc-lower-math"))
    return 1;
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  if (!mlir::PassInfo::lookup("zkc-lower-math") ||
      mlir::PassInfo::lookup("lower-pir-to-plan"))
    return 2;
  mlir::PassManager pipeline(&context);
  return mlir::failed(mlir::parsePassPipeline(
      "builtin.module(zkc-participant-pipeline)", pipeline));
}
