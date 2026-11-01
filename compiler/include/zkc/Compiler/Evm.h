#ifndef ZKC_COMPILER_EVM_H
#define ZKC_COMPILER_EVM_H

#include "mlir/IR/DialectRegistry.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeProof.h"
#include <cstdint>
#include <memory>

namespace zkc {
/// Deployment configuration. The compiler accepts only positive ceilings at or
/// below these defaults. Once compiled, callers cannot supply or raise a
/// budget.
struct EvmLimits {
  uint64_t rounds = 10;
  uint64_t publicElements = 1024;
  uint64_t frameBytes = 65536;
  uint64_t publicBytes = 131072;
  uint64_t contextBytes = 4096;
  uint64_t proofBytes = 65536;
  uint64_t calldataBytes = 262144;
  uint64_t rootBytes = 262144;
  uint64_t memoryBytes = 2097152;
  uint64_t transcriptTransitions = 64;
  uint64_t practicalGas = 20000000;
};

struct EvmOptions {
  /// Explicit logical proof selection. Empty draws are selected by the common
  /// construction checker. compileEvmEntry derives this from CheckedOriginal.
  NativeProofPolicy policy;
  MathematicalSelectionPolicy mathematics = {};
  protocol::OracleRealizationPolicy oracleSelection = {};
  EvmLimits limits;
};

/// Source product, before external solc compilation or deployment validation.
/// Owns its MLIR context; module snapshots borrow it and must not outlive it.
/// Neither snapshots nor metadata grant source/construction authority.
class EvmCompilation {
public:
  EvmCompilation(EvmCompilation &&) noexcept;
  EvmCompilation &operator=(EvmCompilation &&) noexcept;
  ~EvmCompilation();
  const std::string &yul() const;
  const llvm::json::Value &abi() const;
  const llvm::json::Value &descriptor() const;
  const llvm::json::Value &manifest() const;
  const NativeProofPolicy &policy() const;
  const EvmLimits &limits() const;
  llvm::StringRef sourceSha256() const;
  llvm::StringRef sourceBytes() const;
  mlir::OwningOpRef<mlir::ModuleOp> targetSnapshot() const;

private:
  struct Storage;
  std::unique_ptr<Storage> storage;
  explicit EvmCompilation(std::unique_ptr<Storage>);
  friend llvm::Expected<EvmCompilation>
  compileEvmProof(llvm::StringRef, llvm::StringRef, const EvmOptions &,
                  const mlir::DialectRegistry &);
};

/// Parse exact original emitted MLIR bytes, check common construction and
/// closed execution, select/check the validator closure and fully legalize it
/// to EVM. Never selects CPU representations or invokes an external compiler.
llvm::Expected<EvmCompilation> compileEvmProof(llvm::StringRef sourceBytes,
                                               llvm::StringRef filename,
                                               const EvmOptions &,
                                               const mlir::DialectRegistry &);

/// Use the common language frontend and its exact checked original bytes.
llvm::Expected<EvmCompilation>
compileEvmEntry(const language::CheckedOriginal &, const EvmOptions & = {});

/// Canonical JSON source object for the SDK/driver. Format zkc.evm-source/0.
llvm::json::Value encodeEvmCompilation(const EvmCompilation &);
llvm::json::Value encodeEvmLimits(const EvmLimits &);
} // namespace zkc
#endif
