#ifndef ZKC_COMPILER_RUN_H
#define ZKC_COMPILER_RUN_H

#include "zkc/Compiler/Compilation.h"
#include <optional>
#include <string>

namespace zkc {
struct RunOptions {
  std::string entry = "main";
  bool simplify = true;
  bool releaseStorage = false;
  /// Optional representation rewrite; benefit depends on observations and CSE.
  bool fixPolynomialFactors = false;
  /// Independently retained zkc.polynomial-requirements JSON. Presence
  /// enables checking before any mathematical folding; an empty record refuses.
  std::optional<std::string> polynomialRequirements;
  /// Independently retained zkc.public-coin-requirement JSON. Analyze the
  /// unsimplified common source before projection; bind the view to this
  /// bundle.
  std::optional<std::string> publicCoinRequirement;
};
/// Owns the final physical module, including retained statement/interface
/// metadata, and a complete zkc.run bundle for the selected entry.
/// The bundle is supplied execution data, not a source correspondence proof.
struct CompiledRun {
  Compilation compilation;
  std::string bundle;
  /// Present only for checked compilation. Bound to the source, requirements
  /// and exact bundle by identities; hashes are identifiers, not proof.
  std::optional<std::string> correspondence;
  /// zkc.compiled-public-coin: structural view and compilation identities.
  std::optional<std::string> publicCoin;
};
/// Compile mathematical MLIR through the native protocol pipeline. This API
/// enforces 16 MiB text, nesting 64 and 4096-byte entry/filename limits.
/// This invocation owns its mathematical MLIR input and compiled artifact.
/// The final module remains valid with its Compilation. Every failure is an
/// owned CompilationError; no partial executable is returned.
llvm::Expected<CompiledRun> compileRun(llvm::StringRef text,
                                       llvm::StringRef filename,
                                       const RunOptions &,
                                       const mlir::DialectRegistry &);
} // namespace zkc
#endif
