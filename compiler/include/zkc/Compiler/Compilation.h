#ifndef ZKC_COMPILER_COMPILATION_H
#define ZKC_COMPILER_COMPILATION_H
#include "mlir/IR/DialectRegistry.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/LinearContraction.h"
#include <memory>
namespace zkc {
struct CompiledRun;
struct RunOptions;
struct CompiledNativeProof;
struct NativeProofOptions;
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
  const LinearContractionStats &statistics() const;
};
} // namespace zkc
#endif
