#ifndef ZKC_COMPILER_NATIVECOMPILATION_H
#define ZKC_COMPILER_NATIVECOMPILATION_H
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Target/CpuTarget.h"
#include <optional>
#include <variant>
namespace zkc {
enum class NativeProofOperation { Prove, Verify };
struct NativeProofOptions {
  std::variant<std::string, NativeProofSelection> policy;
  bool simplify = true, releaseStorage = false;
  MathematicalSelectionPolicy mathematicalSelection = {};
  /// Absent preserves the existing complete declarative deployment API.
  std::optional<NativeProofOperation> operation = std::nullopt;
  CompilationObservation *observations = nullptr;
  target::CpuTarget cpuTarget = {};
  protocol::OracleRealizationPolicy oracleRealization = {};
};
struct CompiledNativeProof {
  Compilation compilation;
  std::string deployment;
  /// Complete policy after occurrence selection and strict admission.
  NativeProofPolicy policy;
};
/// Owned, source-checked compilation. A host must authenticate the resulting
/// deployment independently; hashes inside a supplied artifact are not
/// authority.
llvm::Expected<CompiledNativeProof>
compileNativeProof(llvm::StringRef source, llvm::StringRef filename,
                   const NativeProofOptions &options,
                   const mlir::DialectRegistry &registry);
} // namespace zkc
#endif
