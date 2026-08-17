//===- zkc-seal.cpp - The seal driver ---------------------------*- C++ -*-===//
// The driver owns all IO (docs/spec/carrier.md §5): parse → verify →
// pir-seal → write each sealed protocol as `<id>.mlirbc` into the output
// directory. The seal pass itself touches no file beyond the registry it
// is given; artifacts written by this binary carry the zkc producer
// string and the dialect version blob.
//===----------------------------------------------------------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Support/FileUtilities.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/Artifact/SealedGuard.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Dialect/Pir/Transforms/Passes.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/ToolOutputFile.h"

using namespace llvm;
using namespace mlir;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<protocols.mlir>"));
static cl::opt<std::string> protocolVocabulary(
    "protocol-vocabulary", cl::Required,
    cl::desc("Path to the cross-admitted ProtocolVocabulary JSON file"));
static cl::opt<std::string> constructionProfileRegistry(
    "construction-profile-registry", cl::init(""),
    cl::desc("Path to the construction-profile registry JSON file "
             "(required when kappa consumes a sponge or codec)"));
// Sealing writes one artifact per protocol in the module, so its
// destination is a directory where every sibling tool's `-o` is a file.
// One letter meaning two things across a tool family is a mistake a
// caller makes silently — a path that was meant as a file becomes a
// directory — so the directory has its own name and `-o` stays as an
// alias for the callers that already spell it.
static cl::opt<std::string>
    outputDir("output-dir", cl::Required,
              cl::desc("Directory the artifacts are written into"));
static cl::alias outputDirShort("o", cl::aliasopt(outputDir), cl::Hidden);

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv, "zkc-seal: seal protocols and write their artifacts\n");

  MLIRContext context;
  context.loadDialect<zkc::pir::PirDialect>();
  // Sealed protocols live in this context once the pass has run; any
  // pattern-driven pass added to this driver later must refuse beneath
  // them (docs/spec/carrier.md §5).
  zkc::installSealedGuard(context);

  zkc::tool::ParsedModule parsed =
      zkc::tool::parseModule(inputFilename, context);
  if (!parsed)
    return 1;
  ModuleOp module = parsed.get();

  PassManager passManager(&context);
  zkc::pir::PirSealOptions options;
  options.protocolVocabulary = protocolVocabulary;
  options.constructionProfileRegistry = constructionProfileRegistry;
  passManager.addPass(zkc::pir::createPirSeal(options));
  if (failed(passManager.run(module)))
    return 1;

  if (std::error_code error = llvm::sys::fs::create_directories(outputDir)) {
    return zkc::tool::reportError("cannot create '" + outputDir + "': " +
                                  error.message());
  }
  // Every artifact writes before any is kept: a failure mid-module
  // leaves no partial output set behind.
  SmallVector<std::unique_ptr<ToolOutputFile>> outputs;
  for (zkc::pir::SealedOp sealed : module.getOps<zkc::pir::SealedOp>()) {
    SmallString<256> path(outputDir.getValue());
    llvm::sys::path::append(path, sealed.getId() + ".mlirbc");
    std::string error;
    std::unique_ptr<ToolOutputFile> output = openOutputFile(path, &error);
    if (!output) {
      return zkc::tool::reportError(error);
    }
    if (failed(zkc::artifact::writeArtifact(sealed, output->os())))
      return 1;
    outs() << path << "\n";
    outputs.push_back(std::move(output));
  }
  for (auto &output : outputs)
    output->keep();
  return 0;
}
