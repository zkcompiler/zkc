#ifndef ZKC_COMPILER_RUN_H
#define ZKC_COMPILER_RUN_H

#include "zkc/Compiler/Compilation.h"
#include "zkc/Target/CpuTarget.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/OracleSelection.h"
#include <optional>
#include <string>

namespace zkc {
class CompilationObservation;
struct RunOptions {
  std::string entry = "main";
  bool simplify = true;
  bool releaseStorage = false;
  /// Optional representation rewrite; benefit depends on observations and CSE.
  bool fixPolynomialFactors = false;
  /// Independently retained zkc.polynomial-requirements/0 JSON. Presence
  /// enables checking before any mathematical folding; an empty record refuses.
  std::optional<std::string> polynomialRequirements;
  /// Independently retained zkc.public-coin-requirement/0 JSON. Analyze the
  /// selected authored or realized subject through the existing checked owner
  /// before projection; bind the view to this bundle.
  std::optional<std::string> publicCoinRequirement;
  /// Mathematical algorithm families, independent of simplify/storage release.
  MathematicalSelectionPolicy mathematicalSelection = {};
  CompilationObservation *observations = nullptr;
  target::CpuTarget cpuTarget = {};
  /// Common oracle representation, before participant and physical selection.
  protocol::OracleRealizationPolicy oracleRealization = {};
};
/// Owns the final physical module, the original-to-realized common edge, and a
/// complete zkc.run/0 bundle for the selected entry. Logical oracle clauses
/// stay on the retained original; native interfaces describe representation
/// leaves. The bundle is supplied execution data, not a source correspondence
/// proof.
struct CompiledRun {
  Compilation compilation;
  std::string bundle;
  /// Present only for checked compilation. Bound to the source, requirements
  /// and exact bundle by identities; hashes are identifiers, not proof.
  std::optional<std::string> correspondence;
  /// zkc.compiled-public-coin/0: structural view and compilation identities.
  std::optional<std::string> publicCoin;
};
/// Compile Protocol IR through the native protocol pipeline. This API
/// enforces 16 MiB text, nesting 64 and 4096-byte entry/filename limits.
/// This invocation owns its Protocol IR input and compiled artifact.
/// The final module remains valid with its Compilation. Every failure is an
/// owned CompilationError; no partial executable is returned.
llvm::Expected<CompiledRun> compileRun(llvm::StringRef text,
                                       llvm::StringRef filename,
                                       const RunOptions &,
                                       const mlir::DialectRegistry &);
} // namespace zkc
#endif
