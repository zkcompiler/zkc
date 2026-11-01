#ifndef ZKC_COMPILER_NATIVELANGUAGE_H
#define ZKC_COMPILER_NATIVELANGUAGE_H
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeCompilation.h"
#include "zkc/Compiler/Run.h"
#include <variant>
namespace zkc::language {
struct EntryOptions {
  bool simplify = true;
  bool releaseStorage = false;
  MathematicalSelectionPolicy mathematicalSelection = {};
  CompilationObservation *observations = nullptr;
  target::CpuTarget cpuTarget = {};
  protocol::OracleRealizationPolicy oracleRealization = {};
};
struct CompiledHost {
  std::string artifact;
};
using EntryArtifact =
    std::variant<CompiledRun, CompiledNativeProof, CompiledHost>;
class CompiledEntry {
public:
  const CheckedOriginal &original() const { return source; }
  const EntryArtifact &artifact() const { return compiled; }
  const EntryOptions &options() const { return configuration; }
  /// Exact selected run bundle or proof deployment, as identified by
  /// artifact().
  llvm::StringRef bytes() const;

private:
  CompiledEntry(CheckedOriginal source, EntryArtifact compiled,
                EntryOptions options)
      : source(std::move(source)), compiled(std::move(compiled)),
        configuration(options) {
    configuration.observations = nullptr;
  }
  CheckedOriginal source;
  EntryArtifact compiled;
  EntryOptions configuration;
  friend llvm::Expected<CompiledEntry> compileEntry(const CheckedOriginal &,
                                                    const EntryOptions &);
};
/// Compile the explicitly selected run or proof job. Derived challenge
/// occurrences are resolved through native construction admission. Uses the
/// built-in registry; caller extensions cannot replace its models.
llvm::Expected<CompiledEntry> compileEntry(const CheckedOriginal &,
                                           const EntryOptions & = {});

llvm::Expected<CompiledHost> compileHost(const CheckedOriginal &,
                                         const EntryOptions &);
} // namespace zkc::language
#endif
