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

int reportError(llvm::Error error) {
  return reportError(llvm::toString(std::move(error)));
}

int reportError(const llvm::Twine &message) {
  llvm::errs() << "error: " << message << "\n";
  return 1;
}

} // namespace tool
} // namespace zkc
