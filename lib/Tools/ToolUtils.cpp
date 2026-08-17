//===- ToolUtils.cpp - shared driver plumbing -------------------*- C++ -*-===//
#include "zkc/Tools/ToolUtils.h"

#include "mlir/Bytecode/BytecodeReader.h"
#include "mlir/Parser/Parser.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;

namespace zkc {
namespace tool {

ParsedModule parseModule(llvm::StringRef path, MLIRContext &context) {
  ParsedModule parsed;
  parsed.sourceMgr = std::make_shared<llvm::SourceMgr>();
  parsed.handler =
      std::make_unique<SourceMgrDiagnosticHandler>(*parsed.sourceMgr, &context);
  auto input = llvm::MemoryBuffer::getFileOrSTDIN(path);
  if (!input) {
    emitError(UnknownLoc::get(&context)) << "cannot read source '" << path
                                         << "': " << input.getError().message();
    return parsed;
  }
  if (isBytecode((*input)->getMemBufferRef())) {
    emitError(UnknownLoc::get(&context))
        << "source parser " << kBytecodeRefusal;
    return parsed;
  }
  parsed.sourceMgr->AddNewSourceBuffer(std::move(*input), llvm::SMLoc());
  parsed.module = parseSourceFile<ModuleOp>(*parsed.sourceMgr, &context);
  return parsed;
}

/// One spelling on stderr for both, because a reader scanning output
/// should recognize a failure without knowing which binary produced it.
/// The exit code, not the prefix, is what tells the two apart, and the
/// message says which happened.
static int report(const llvm::Twine &message, int code) {
  llvm::errs() << "error: " << message << "\n";
  return code;
}

int reportRefusal(llvm::Error error) {
  return reportRefusal(llvm::toString(std::move(error)));
}
int reportRefusal(const llvm::Twine &message) { return report(message, 1); }

int reportCannotAnswer(llvm::Error error) {
  return reportCannotAnswer(llvm::toString(std::move(error)));
}
int reportCannotAnswer(const llvm::Twine &message) {
  return report(message, 2);
}

} // namespace tool
} // namespace zkc
