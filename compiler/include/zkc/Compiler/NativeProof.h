#ifndef ZKC_COMPILER_NATIVEPROOF_H
#define ZKC_COMPILER_NATIVEPROOF_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Compiler/Compilation.h"
#include "llvm/Support/JSON.h"
namespace zkc {
/// Closed versioned deployment policy. The source remains independently owned.
struct NativeProofPolicy {
  std::string entry, producer, validator, suite;
  unsigned version = 1;
  bool iterated() const { return version >= 2; }
  bool committed() const { return version == 3 || version == 4; }
  bool structured() const { return version == 4; }
  unsigned acceptance = 0;
  std::optional<unsigned> service;
  std::vector<unsigned> publicInputs;
  std::vector<std::pair<std::string, std::string>> draws;
};
llvm::Expected<NativeProofPolicy> parseNativeProofPolicy(llvm::StringRef text);
llvm::json::Value encodeNativeProofPolicy(const NativeProofPolicy &policy);
struct NativeProofConstruction {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  llvm::json::Value descriptor;
  /// Source message origin to lowered wire site; excluded from transcript
  /// roots.
  llvm::json::Array wireSites;
};
/// Admit original source, prepare/project without simplification and construct
/// role-local transcripts. No source IR is mutated and no cryptographic theorem
/// is asserted. An empty suite selects the authored no-transcript profile.
llvm::Expected<NativeProofConstruction>
constructNativeProof(mlir::ModuleOp source, const NativeProofPolicy &policy);
/// Construct with an independent projected-to-constructed postcondition, then
/// compare the entire supplied candidate, including SSA and retained records,
/// ignoring locations. Source policy/occurrence admission remains a premise.
llvm::Error checkNativeProof(mlir::ModuleOp source, mlir::ModuleOp candidate,
                             const NativeProofPolicy &policy);
struct NativeProofOptions {
  std::string policy;
  bool simplify = true, releaseStorage = false;
};
struct CompiledNativeProof {
  Compilation compilation;
  std::string deployment;
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
