#ifndef ZKC_DIALECT_EXEC_RESOURCE_ORIGINS_H
#define ZKC_DIALECT_EXEC_RESOURCE_ORIGINS_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/Support/Error.h"
#include <map>
#include <memory>
namespace zkc::protocol {
struct SourceExecutionClosure;
}
namespace zkc::exec {
/// Exact affine result roots relative to data formals (the scope is excluded).
/// Missing roots mean unknown; a stopped body has no continuing results. Height
/// includes nested control and calls even when a summary is reused.
struct ResourceOriginSummary {
  std::map<unsigned, unsigned> roots;
  bool continues = true;
  unsigned depth = 1;
};
/// Derived facts over one immutable logical native closure after structure,
/// symbols and affine use have been admitted. Finite-state obligations may
/// still be pending. Owns the SSA/control association, not IR or a serialized
/// Program snapshot. Changing bodies, ports, callees or declarations
/// invalidates the instance. The shared caller-owned work allowance must
/// outlive it; no query replenishes it.
class ResourceOriginAnalysis {
  struct Impl;
  std::unique_ptr<Impl> impl;
  explicit ResourceOriginAnalysis(std::unique_ptr<Impl>);

public:
  ~ResourceOriginAnalysis();
  static llvm::Expected<std::unique_ptr<ResourceOriginAnalysis>>
  create(mlir::Operation *owner, protocol::SourceExecutionClosure closure,
         uint64_t &remaining, unsigned depthLimit = 64);
  llvm::Expected<ResourceOriginSummary> get(mlir::func::FuncOp function,
                                            unsigned depth = 1);
  /// Inspect every actual ordered fold, including dormant requests. Complete
  /// structure, callback ABI, affine use and acyclicity must already be
  /// checked.
  llvm::Error verifyFiniteState();
};
} // namespace zkc::exec
#endif
