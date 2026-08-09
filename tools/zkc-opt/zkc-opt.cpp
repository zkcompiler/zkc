//===- zkc-opt.cpp - Protocol IR optimizer driver ---------------*- C++ -*-===//
#include "mlir/Bytecode/BytecodeReader.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Support/FileUtilities.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Artifact/SealedGuard.h"
#include "zkc/Dialect/Oir/OirDialect.h"
#include "zkc/Dialect/Pir/PirDialect.h"
#include "zkc/Dialect/Pir/Transforms/Passes.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/ToolOutputFile.h"

#ifdef ZKC_ENABLE_TEST_PASSES
namespace zkc {
namespace test {
void registerTestArtifactLifecyclePass();
void registerTestCompilerCorePass();
void registerTestHoleParametersPass();
void registerTestInterpreterPass();
void registerTestKzgBatchCorePass();
void registerTestPirCompilerProviderPass();
void registerTestSealEnginePass();
void registerTestSealedGuardPass();
void registerTestSoundnessCatalogPass();
void registerTestSoundnessEvaluatorPass();
void registerTestSoundnessKernelPass();
void registerTestSoundnessKzgPreservationPass();
void registerTestSoundnessProjectionPass();
void registerTestSoundnessRuntimePass();
void registerTestSoundnessRuleBodiesPass();
void registerTestSoundnessSemanticRegressionsPass();
void registerTestSoundnessSitePass();
} // namespace test
} // namespace zkc
#endif

int main(int argc, char **argv) {
  llvm::InitLLVM init(argc, argv);

  // Generic transforms (canonicalize/cse/sccp/...) are registered on
  // purpose: protocol content must survive them byte-identically —
  // token threading plus the protocol side-effect resource make that
  // structural (docs/spec/carrier.md §3), and the chain-safety
  // regression keeps it empirical.
  mlir::registerTransformsPasses();
  zkc::pir::registerPirPasses();
#ifdef ZKC_ENABLE_TEST_PASSES
  zkc::test::registerTestArtifactLifecyclePass();
  zkc::test::registerTestCompilerCorePass();
  zkc::test::registerTestHoleParametersPass();
  zkc::test::registerTestInterpreterPass();
  zkc::test::registerTestKzgBatchCorePass();
  zkc::test::registerTestPirCompilerProviderPass();
  zkc::test::registerTestSealEnginePass();
  zkc::test::registerTestSealedGuardPass();
  zkc::test::registerTestSoundnessCatalogPass();
  zkc::test::registerTestSoundnessEvaluatorPass();
  zkc::test::registerTestSoundnessKernelPass();
  zkc::test::registerTestSoundnessKzgPreservationPass();
  zkc::test::registerTestSoundnessProjectionPass();
  zkc::test::registerTestSoundnessRuntimePass();
  zkc::test::registerTestSoundnessRuleBodiesPass();
  zkc::test::registerTestSoundnessSemanticRegressionsPass();
  zkc::test::registerTestSoundnessSitePass();
#endif

  mlir::DialectRegistry registry;
  registry.insert<zkc::pir::PirDialect, zkc::oir::OirDialect,
                  mlir::func::FuncDialect>();
  // A context that can parse sealed IR and run pattern-driven passes must
  // carry the sealed guard before any pipeline runs (docs/spec/carrier.md
  // §5). MlirOptMain owns its contexts, so installation rides the dialect
  // load instead of a direct call.
  registry.addExtension(
      +[](mlir::MLIRContext *context, zkc::pir::PirDialect *) {
        zkc::installSealedGuard(*context);
      });

  auto [inputFilename, outputFilename] = mlir::registerAndParseCLIOptions(
      argc, argv,
#ifdef ZKC_ENABLE_TEST_PASSES
      "zkc-test-opt: textual Protocol IR test driver",
#else
      "zkc-opt: textual Protocol IR driver",
#endif
      registry);
  mlir::MlirOptMainConfig config =
      mlir::MlirOptMainConfig::createFromCLOptions();

  if (config.shouldShowDialects() || config.shouldListPasses()) {
    auto empty = llvm::MemoryBuffer::getMemBuffer("");
    return mlir::asMainReturnCode(
        mlir::MlirOptMain(llvm::outs(), std::move(empty), registry, config));
  }

  // zkc-opt is the transient compiler-IR driver, not an artifact reader.
  // Persisted PIR crosses the trust boundary only through the artifact loader;
  // accepting arbitrary MLIR bytecode here would create an undeclared route
  // around its producer, dialect-version, shape, and identity checks.
  std::string error;
  std::unique_ptr<llvm::MemoryBuffer> input =
      mlir::openInputFile(inputFilename, &error);
  if (!input) {
    llvm::errs() << error << "\n";
    return 1;
  }
  if (mlir::isBytecode(input->getMemBufferRef())) {
    llvm::errs() << "zkc-opt " << zkc::tool::kBytecodeRefusal << "\n";
    return 1;
  }

  std::unique_ptr<llvm::ToolOutputFile> output =
      mlir::openOutputFile(outputFilename, &error);
  if (!output) {
    llvm::errs() << error << "\n";
    return 1;
  }
  if (mlir::failed(
          mlir::MlirOptMain(output->os(), std::move(input), registry, config)))
    return 1;
  output->keep();
  return 0;
}
