#ifndef ZKC_COMPILER_COMPILATIONSTATE_H
#define ZKC_COMPILER_COMPILATIONSTATE_H
#include "mlir/IR/Location.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Dialect/Registry.h"
namespace zkc {
struct Compilation::Storage {
  mlir::MLIRContext context;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  LinearContractionStats statistics;
  explicit Storage(const mlir::DialectRegistry &registry) : context(registry) {
    mlir::DialectRegistry builtins;
    registerDialects(builtins);
    context.appendDialectRegistry(builtins);
    context.printOpOnDiagnostic(false);
  }
};
namespace detail {
void collectError(const llvm::Error &, std::vector<diagnostics::RefusalInfo> &,
                  std::vector<DiagnosticLocation> &,
                  std::vector<InvocationPrecondition> &);
llvm::Error compilationError(llvm::Error);
/// Collect diagnostics while their context lives. Do not recover codes from
/// prose. A module-level pass refusal keeps the CLI's unlocated rendering.
class Diagnostics {
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  std::vector<InvocationPrecondition> preconditions;
  std::optional<mlir::Location> root;
  bool sawError = false;
  mlir::ScopedDiagnosticHandler handler;

public:
  explicit Diagnostics(mlir::MLIRContext &context)
      : handler(&context, [&](mlir::Diagnostic &diagnostic) {
          // Match the default MLIR handler: warnings and remarks do not turn
          // a successful invocation into an error or leak to process stderr.
          if (diagnostic.getSeverity() != mlir::DiagnosticSeverity::Error)
            return mlir::success();
          sawError = true;
          if (!message.empty())
            message += '\n';
          llvm::raw_string_ostream out(message);
          if (!root || diagnostic.getLocation() != *root) {
            if (!mlir::isa<mlir::UnknownLoc>(diagnostic.getLocation())) {
              diagnostic.getLocation().print(out);
              out << ": ";
            }
            out << "error: ";
          }
          if (auto location = diagnostic.getLocation()
                                  ->findInstanceOf<mlir::FileLineColLoc>())
            locations.push_back({location.getFilename().str(),
                                 location.getLine(), location.getColumn()});
          diagnostic.print(out);
          for (auto &note : diagnostic.getNotes()) {
            out << '\n';
            if (!mlir::isa<mlir::UnknownLoc>(note.getLocation())) {
              note.getLocation().print(out);
              out << ": ";
            }
            out << "note: ";
            note.print(out);
            if (auto location =
                    note.getLocation()->findInstanceOf<mlir::FileLineColLoc>())
              locations.push_back({location.getFilename().str(),
                                   location.getLine(), location.getColumn()});
          }
          auto metadata = diagnostics::refusals(diagnostic);
          llvm::append_range(refusals, metadata);
          return mlir::success();
        }) {}
  void atRoot(mlir::Location location) { root = location; }
  bool hasErrors() const { return sawError; }
  llvm::Error failure(llvm::Error fallback = llvm::Error::success()) {
    if (fallback) {
      collectError(fallback, refusals, locations, preconditions);
      if (!message.empty())
        message += '\n';
      message += llvm::toString(std::move(fallback));
    }
    if (message.empty())
      message = "pass pipeline failed without an error diagnostic";
    return llvm::make_error<CompilationError>(
        std::move(message), std::move(refusals), std::move(locations),
        std::move(preconditions));
  }
};
} // namespace detail
} // namespace zkc
#endif
