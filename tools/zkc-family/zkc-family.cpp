//===- zkc-family.cpp - family instance generation --------------*- C++ -*-===//
// One declarative instance description in, two artifacts out: the closed
// ProtocolVocabulary and the PIR spine. The generator is unjudged —
// everything it writes goes through the ordinary seal battery — so this
// driver's own gates are for error locality, not trust: the emitted
// vocabulary must admit through its real loader and the emitted spine must
// parse through the real dialect before any file is written. The sweep path
// links the library and generates in-process; this binary is its lit-testable
// shell.
//===----------------------------------------------------------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Family/FriFamily.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/ToolOutputFile.h"

using namespace llvm;

static cl::opt<std::string> inputFilename(cl::Positional, cl::Required,
                                          cl::desc("<description.json>"));
static cl::opt<std::string>
    emitVocabulary("emit-vocabulary", cl::Required,
                   cl::desc("Path the ProtocolVocabulary is written to"));
static cl::opt<std::string>
    emitSpine("emit-spine", cl::Required,
              cl::desc("Path the PIR spine is written to"));

static void printParamSurface(raw_ostream &os) {
  os << "fri instance description fields:\n";
  for (const zkc::family::ParamSpec &spec : zkc::family::friParamSpecs())
    os << "  " << spec.name << (spec.required ? " (required): " : ": ")
       << spec.doc << "\n";
}

static Error writeFile(StringRef path, StringRef contents) {
  std::error_code ec;
  ToolOutputFile out(path, ec, sys::fs::OF_Text);
  if (ec)
    return createStringError("cannot write '" + path + "': " + ec.message());
  out.os() << contents;
  out.keep();
  return Error::success();
}

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv,
      "zkc-family: emit one family instance (vocabulary + spine) from a "
      "declarative description\n\n\nExit: 0 the answer is yes, 1 the subject "
      "was examined and the answer is no, 2 the invocation never reached its "
      "subject (docs/getting-started.md).\n");

  auto buffer = MemoryBuffer::getFile(inputFilename, /*IsText=*/true);
  if (!buffer)
    return zkc::tool::reportCannotAnswer(
        llvm::Twine("[zkc-E900] ") +
        llvm::toString(createStringError("cannot read '" +
                                         StringRef(inputFilename) +
                                         "': " + buffer.getError().message())));

  auto description =
      zkc::family::parseFriDescription((*buffer)->getBuffer(), inputFilename);
  if (!description) {
    int exit = zkc::tool::reportRefusal(description.takeError());
    printParamSurface(errs());
    return exit;
  }

  // Emit, then self-check through the real consumers before writing —
  // a template bug is named here, at the tool, not later at seal.
  std::string vocabulary = zkc::family::emitFriVocabulary(*description);
  auto admitted = zkc::registry::ProtocolVocabulary::parse(
      vocabulary, "generated protocol vocabulary");
  if (!admitted)
    return zkc::tool::reportCannotAnswer(
        llvm::Twine("[zkc-E904] ") +
        llvm::toString(createStringError(
            "internal template error (the emitted registry does not admit): " +
            toString(admitted.takeError()))));

  std::string spine = zkc::family::emitFriSpine(*description);
  mlir::MLIRContext context;
  context.loadDialect<zkc::pir::PirDialect>();
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceString<mlir::ModuleOp>(spine, &context);
  if (!module)
    return zkc::tool::reportCannotAnswer(
        llvm::Twine("[zkc-E904] ") +
        llvm::toString(createStringError(
            "internal template error (the emitted spine does not parse)")));

  if (Error err = writeFile(emitVocabulary, vocabulary))
    return zkc::tool::reportRefusal(std::move(err));
  if (Error err = writeFile(emitSpine, spine))
    return zkc::tool::reportRefusal(std::move(err));
  return 0;
}
