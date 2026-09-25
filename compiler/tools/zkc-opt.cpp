#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Transforms/Passes.h"
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
