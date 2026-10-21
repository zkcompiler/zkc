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
  explicit CompilationObservation(std::vector<std::string> dumps = {});
  ~CompilationObservation();
  void phase(llvm::StringRef, mlir::ModuleOp);
  void instrument(mlir::PassManager &);
  void decisions(mlir::ModuleOp, const mathematical::RealizationTrace &);
  llvm::json::Value json() const;
};
} // namespace zkc
#endif
