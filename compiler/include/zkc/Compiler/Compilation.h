#ifndef ZKC_COMPILER_COMPILATION_H
#define ZKC_COMPILER_COMPILATION_H
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/LinearContraction.h"
#include <memory>
#include <optional>
#include <string>
namespace zkc {
struct CompiledRun;
struct RunOptions;
struct CompiledNativeProof;
struct NativeProofOptions;
/// Independent prepared-source/candidate inspection copies, not checked-stage
/// authority. Both modules
/// borrow the Compilation's context and must die before it is destroyed or
/// reassigned. The record owns its bytes. Mutations do not affect the retained
/// edge and must be rechecked before relying on correspondence.
struct OracleRealizationSnapshot {
  mlir::OwningOpRef<mlir::ModuleOp> prepared, candidate;
  std::string record;
};
/// Owns a native compilation's context and IR. Borrowed module access lasts
/// until destruction or reassignment; mutation invalidates prior conclusions.
class Compilation {
  struct Storage;
  std::unique_ptr<Storage> storage;
  explicit Compilation(std::unique_ptr<Storage>);
  friend llvm::Expected<CompiledRun> compileRun(llvm::StringRef,
                                                llvm::StringRef,
                                                const RunOptions &,
                                                const mlir::DialectRegistry &);
  friend llvm::Expected<CompiledNativeProof>
  compileNativeProof(llvm::StringRef, llvm::StringRef,
                     const NativeProofOptions &, const mlir::DialectRegistry &);

public:
  Compilation(Compilation &&) noexcept;
  Compilation &operator=(Compilation &&) noexcept;
  ~Compilation();
  mlir::ModuleOp module() const;
  /// Present for joint-run compilation, including the ordinary identity edge.
  /// It describes preparation to common realization, not later optimization,
  /// logical-predicate transport, or a cryptographic simulation theorem.
  std::optional<OracleRealizationSnapshot> oracleRealizationSnapshot() const;
  const LinearContractionStats &statistics() const;
};
} // namespace zkc
#endif
