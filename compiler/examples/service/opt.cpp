#include "Service.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Transforms/Passes.h"
int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  zkc::service::registerService(registry);
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  mlir::registerTransformsPasses();
  return mlir::asMainReturnCode(mlir::MlirOptMain(
      argc, argv, "zkc service example optimizer\n", registry));
}
