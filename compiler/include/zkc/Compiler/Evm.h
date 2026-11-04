#ifndef ZKC_COMPILER_EVM_H
#define ZKC_COMPILER_EVM_H

#include "mlir/IR/DialectRegistry.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Target/Evm/Declaration.h.inc"
#include <cstdint>
#include <memory>

namespace zkc {
namespace evm {
struct EvmEndpoint;
} // namespace evm
/// Exact external deployment setting; no arbitrary solc version string. The
/// forks are the rows of the installed zkc.evm-target/0 declaration.
enum class EvmFork {
#define ZKC_EVM_FORK_ENUMERATOR(Enumerator, ...) Enumerator,
  ZKC_EVM_TARGET_FORKS(ZKC_EVM_FORK_ENUMERATOR)
#undef ZKC_EVM_FORK_ENUMERATOR
};
llvm::StringRef evmForkName(EvmFork);
llvm::Expected<EvmFork> parseEvmFork(llvm::StringRef);

/// Deployment configuration. The compiler accepts only ceilings within each
/// declared row's minimum and maximum; the defaults are the maxima. Once
/// compiled, callers cannot supply or raise a budget.
struct EvmLimits {
#define ZKC_EVM_LIMIT_MEMBER(member, name, minimum, maximum)                   \
  uint64_t member = maximum;
  ZKC_EVM_TARGET_LIMITS(ZKC_EVM_LIMIT_MEMBER)
#undef ZKC_EVM_LIMIT_MEMBER
};

/// Decode a complete effective selection from bounded inline JSON. Requires
/// exactly the generated names and unique keys, then uses the same range
/// validation as the C++ compilation API. Partial selections belong to the SDK.
llvm::Expected<EvmLimits> parseEvmLimits(llvm::StringRef);

struct EvmOptions {
  /// Explicit logical proof selection. Managed empty draws are selected by the
  /// common checker; the authored empty suite needs no draw selection.
  /// compileEvmEntry derives this from CheckedOriginal.
  NativeProofPolicy policy;
  EvmFork fork = EvmFork::ZKC_EVM_TARGET_DEFAULT_FORK;
  bool simplify = true;
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
  const llvm::json::Value &descriptor() const;
  const NativeProofPolicy &policy() const;
  EvmFork fork() const;
  /// The effective common-stage options, in the shared published list.
  const llvm::json::Value &options() const;
  /// The validated effective deployment ceilings.
  const EvmLimits &limits() const;
  /// The SHA-256 of the exact original bytes: the original's identity.
  llvm::StringRef sourceSha256() const;
  /// The checked endpoint the Yul was exported from.
  const evm::EvmEndpoint &endpoint() const;
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

/// The project facts a source response binds beside the compilation: the
/// selected source Entry, distinct from the policy's entry symbol, and the
/// authored capture and installation identities.
struct EvmSourceIdentity {
  std::string entry;
  std::string capture;
  std::string installation;
};

/// The one producer of zkc.evm-source/0, the canonical JSON source object for
/// the SDK. It names the installed target declaration by identity beside the
/// selected fork, so a reader with a different declaration refuses it. Tool
/// facts (solc, its settings and the verifier ABI) belong to the declaration
/// and the SDK, not to this response.
llvm::json::Value encodeEvmCompilation(const EvmCompilation &,
                                       const EvmSourceIdentity &);
llvm::json::Value encodeEvmLimits(const EvmLimits &);
} // namespace zkc
#endif
