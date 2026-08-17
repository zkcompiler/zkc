//===- ToolUtils.h - shared driver plumbing ---------------------*- C++ -*-===//
// Drivers own IO (docs/spec/carrier.md §5); this is the IO they share:
// parsing a module with source-line diagnostics attached, finding the
// one container a tool operates on, and the one spelling of an error
// exit. A new tool starts here instead of re-growing the skeleton.
//===----------------------------------------------------------------------===//
#ifndef ZKC_TOOLS_TOOLUTILS_H
#define ZKC_TOOLS_TOOLUTILS_H

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/OwningOpRef.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/SourceMgr.h"

#include <memory>

namespace zkc {
namespace tool {

/// The textual-input boundary's one refusal sentence: persisted PIR
/// crosses the trust boundary only through the artifact loader, so
/// every source-facing driver refuses MLIR bytecode with this spelling,
/// prefixed by the refusing subject.
inline constexpr llvm::StringLiteral kBytecodeRefusal =
    "accepts textual compiler IR only; use an artifact consumer for "
    "persisted PIR";

/// A parsed module whose diagnostics render with source lines for the
/// tool's whole lifetime — pass and verifier failures included, not
/// only parse errors — because the handler lives as long as the
/// module does.
struct ParsedModule {
  std::shared_ptr<llvm::SourceMgr> sourceMgr;
  std::unique_ptr<mlir::SourceMgrDiagnosticHandler> handler;
  mlir::OwningOpRef<mlir::ModuleOp> module;

  explicit operator bool() const { return static_cast<bool>(module); }
  mlir::ModuleOp get() { return *module; }
};

/// Parse one textual .mlir source ("-" is stdin) with the source-manager
/// diagnostic handler installed. MLIR bytecode is refused here: persisted
/// sealed artifacts cross only `artifact::loadArtifact`, so a source-facing
/// tool can never decode or re-emit an older artifact format.
ParsedModule parseModule(llvm::StringRef path, mlir::MLIRContext &context);

/// The one container this tool operates on, selected by predicate —
/// for tools whose container may be one of several op types: exactly
/// one matching op at module top level, or a module-level error naming
/// `what`.
inline mlir::Operation *
getSingleOp(mlir::ModuleOp module, llvm::StringRef what,
            llvm::function_ref<bool(mlir::Operation &)> matches) {
  mlir::Operation *found = nullptr;
  for (mlir::Operation &op : module.getBody()->getOperations()) {
    if (!matches(op))
      continue;
    if (found) {
      module.emitError("expected exactly one ") << what;
      return nullptr;
    }
    found = &op;
  }
  if (!found)
    module.emitError("expected exactly one ") << what;
  return found;
}

/// The one container this tool operates on: exactly one op of type
/// OpT at module top level, or a module-level error naming `what`.
template <typename OpT>
OpT getSingleOp(mlir::ModuleOp module, llvm::StringRef what) {
  mlir::Operation *found = getSingleOp(
      module, what, [](mlir::Operation &op) { return llvm::isa<OpT>(op); });
  return found ? llvm::cast<OpT>(found) : OpT();
}

/// Print an error to stderr in the tools' one spelling and return the
/// failure exit code. Every failure exit in `tools/` goes through here,
/// including the ones that have no `llvm::Error` to carry: a caller
/// reading stderr should not have to know which binary produced a line
/// in order to recognize it as a failure, and a tool that spells its
/// own exit is a tool whose spelling drifts.
int reportError(llvm::Error error);
int reportError(const llvm::Twine &message);

} // namespace tool
} // namespace zkc

#endif // ZKC_TOOLS_TOOLUTILS_H
