//===- zkc-artifact.cpp - Fail-closed artifact inspection -------*- C++ -*-===//
// Loads one persisted artifact through the sole artifact gate. Artifact
// creation belongs to zkc-seal; this tool deliberately has no conversion/write
// mode.
//===----------------------------------------------------------------------===//

#include "zkc/Artifact/Artifact.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"

using namespace llvm;
using namespace mlir;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<PIR artifact>"));
static cl::opt<std::string>
    expectedId("expect-id", cl::init(""),
               cl::desc("Identity the loaded artifact must carry"));

static int load() {
  Expected<zkc::artifact::DecodedPirArtifact> loaded =
      zkc::artifact::loadArtifact(inputFilename, expectedId);
  if (!loaded)
    return zkc::tool::reportRefusal(loaded.takeError());
  outs() << "decoded artifact " << loaded->id() << "\n";
  loaded->print(outs());
  outs() << "\n";
  return 0;
}

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv,
      "zkc-artifact: inspect one PIR artifact\n\n\nExit: 0 the answer is yes, "
      "1 the subject was examined and the answer is no, 2 the invocation never "
      "reached its subject (docs/getting-started.md).\n");
  return load();
}
