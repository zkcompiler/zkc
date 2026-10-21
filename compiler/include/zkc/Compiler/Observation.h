#ifndef ZKC_COMPILER_OBSERVATION_H
#define ZKC_COMPILER_OBSERVATION_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/Support/JSON.h"
#include <memory>
#include <vector>
namespace mlir {
class PassManager;
}
namespace zkc {
/// Optional, invocation-local diagnostic journal. Never an admission
/// certificate. One synchronous compilation owns each observer; pass callbacks
/// synchronize locally. No runtime origin or executable field is modified.
class CompilationObservation {
  struct Storage;
  std::unique_ptr<Storage> storage;

public:
  /// Identify nested application calculations and child deployments in one
  /// bounded journal. The scope never changes executable identity or policy.
  class Scope {
    CompilationObservation *owner = nullptr;
    friend class CompilationObservation;
    Scope(CompilationObservation &, llvm::StringRef);

  public:
    Scope() = default;
    Scope(const Scope &) = delete;
    Scope &operator=(const Scope &) = delete;
    ~Scope();
  };
  Scope scope(llvm::StringRef);
  llvm::json::Value unit() const;
  explicit CompilationObservation(std::vector<std::string> dumps = {});
  ~CompilationObservation();
  void phase(llvm::StringRef, mlir::ModuleOp);
  void instrument(mlir::PassManager &);
  void decisions(mlir::ModuleOp, const mathematical::RealizationTrace &);
  llvm::json::Value json() const;
};
} // namespace zkc
#endif
