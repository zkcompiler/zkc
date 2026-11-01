#include "mlir/IR/DialectRegistry.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "mlir/Support/FileUtilities.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Target/Cpu/Passes.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/ToolOutputFile.h"
int main(int argc, char **argv) {
  llvm::InitLLVM initialization(argc, argv);
  llvm::cl::SetVersionPrinter([](llvm::raw_ostream &out) {
    out << "zkc-opt " << ZKC_VERSION << " (LLVM " << LLVM_VERSION_STRING
        << ")\n";
  });
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  zkc::registerCpuPasses();
  zkc::registerCpuPipelines();
  mlir::registerTransformsPasses();
  auto [inputPath, outputPath] = mlir::registerAndParseCLIOptions(
      argc, argv, "zkc protocol optimizer\n", registry);
  auto options = mlir::MlirOptMainConfig::createFromCLOptions();
  auto config = options;
  config.setPassPipelineSetupFn([options](mlir::PassManager &pm) {
    // A generic pass may erase dormant malformed semantics. Admit before the
    // requested pipeline, even when it contains only upstream transformations.
    // MLIR installs textual reproducer passes before this callback. Preserve
    // their registered descriptions and reparse them behind admission. clear()
    // retains the manager's reproducer-configured verification/threading flags.
    std::string reproduced;
    llvm::raw_string_ostream stream(reproduced);
    llvm::interleaveComma(pm.getPasses(), stream, [&](mlir::Pass &pass) {
      pass.printAsTextualPipeline(stream);
    });
    pm.clear();
    pm.addPass(zkc::createAdmitStagePass());
    if (!reproduced.empty() &&
        mlir::failed(mlir::parsePassPipeline(reproduced, pm, llvm::errs())))
      return mlir::failure();
    if (mlir::failed(options.setupPassPipeline(pm)))
      return mlir::failure();
    pm.addPass(zkc::createAdmitStagePass());
    return mlir::success();
  });
  if (config.shouldShowDialects() || config.shouldListPasses())
    return mlir::asMainReturnCode(mlir::MlirOptMain(
        llvm::outs(), llvm::MemoryBuffer::getMemBuffer(""), registry, config));
  std::string error;
  auto input = mlir::openInputFile(inputPath, &error);
  if (!input) {
    llvm::errs() << error << '\n';
    return 1;
  }
  auto output = mlir::openOutputFile(outputPath, &error);
  if (!output) {
    llvm::errs() << error << '\n';
    return 1;
  }
  if (mlir::failed(
          mlir::MlirOptMain(output->os(), std::move(input), registry, config)))
    return 1;
  output->keep();
  return 0;
}
