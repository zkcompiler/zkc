//===- zkc-project.cpp - persisted PIR endpoint projection -----*- C++ -*-===//
// Production projection accepts one PIR artifact, admits it against one exact
// protocol environment, and emits exactly one OIR artifact.
//===----------------------------------------------------------------------===//

#include "mlir/Support/FileUtilities.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/Dialect/Pir/Transforms/Projection.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/ToolOutputFile.h"

#include <memory>
#include <string>
#include <utility>

namespace cl = llvm::cl;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<PIR artifact>"));
static cl::opt<std::string>
    endpointKind("endpoint-kind", cl::Required,
                 cl::desc("Endpoint kind: verifier or prover_skeleton"));
static cl::opt<std::string> protocolVocabulary(
    "protocol-vocabulary", cl::Required,
    cl::desc("Path to the cross-admitted ProtocolVocabulary JSON file"));
static cl::opt<std::string> constructionProfileRegistry(
    "construction-profile-registry", cl::Required,
    cl::desc("Path to the construction-profile registry JSON file"));
static cl::opt<std::string> outputFilename("o", cl::init("-"),
                                           cl::desc("Output filename"));

int main(int argc, char **argv) {
  llvm::InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv, "zkc-project: project one admitted PIR artifact to OIR\n");

  auto kind = zkc::pir::parseEndpointKind(endpointKind);
  if (!kind)
    return zkc::tool::reportRefusal(kind.takeError());

  auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
      protocolVocabulary, constructionProfileRegistry);
  if (!environment)
    return zkc::tool::reportCannotAnswer(environment.takeError());

  auto admitted = zkc::artifact::loadAndAdmitArtifact(inputFilename,
                                                      std::move(*environment));
  if (!admitted)
    return zkc::tool::reportRefusal(admitted.takeError());

  auto projected = zkc::pir::projectArtifact(*admitted, *kind);
  if (!projected)
    return zkc::tool::reportRefusal(projected.takeError());

  std::string error;
  std::unique_ptr<llvm::ToolOutputFile> output =
      mlir::openOutputFile(outputFilename, &error);
  if (!output) {
    return zkc::tool::reportCannotAnswer(error);
  }
  projected->print(output->os());
  output->os() << "\n";
  output->keep();
  return 0;
}
