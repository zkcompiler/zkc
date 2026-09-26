#include "mlir/IR/DialectRegistry.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/TableLibrary.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/CommandLine.h"
int main(int argc, char **argv) {
  llvm::cl::SetVersionPrinter([](llvm::raw_ostream &out) {
    out << "zkc-opt " << ZKC_VERSION << " (LLVM " << LLVM_VERSION_STRING
        << ")\n";
  });
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  zkc::registerTableLibrary(registry);
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  mlir::registerTransformsPasses();
  return mlir::asMainReturnCode(
      mlir::MlirOptMain(argc, argv, "zkc protocol optimizer\n", registry));
}
