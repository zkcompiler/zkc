#ifndef ZKC_TRANSFORMS_ENDPOINTCLOSURE_H
#define ZKC_TRANSFORMS_ENDPOINTCLOSURE_H
#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/Error.h"
#include <string>
namespace mlir {
class Pass;
}
namespace zkc {
/// Owns an independently checked closed-Exec endpoint edge. Both snapshots
/// borrow the caller's context. The complete source retains correspondence
/// records; only the selected executable inventory is a target support subject.
/// Editing a snapshot never edits or grants authority over the retained edge.
class CheckedEndpoint {
  mlir::OwningOpRef<mlir::ModuleOp> source, candidate;
  std::string selectedRole;
  CheckedEndpoint(mlir::OwningOpRef<mlir::ModuleOp> source,
                  mlir::OwningOpRef<mlir::ModuleOp> candidate, std::string role)
      : source(std::move(source)), candidate(std::move(candidate)),
        selectedRole(std::move(role)) {}
  friend llvm::Expected<CheckedEndpoint> closeEndpoint(mlir::ModuleOp,
                                                       llvm::StringRef);

public:
  mlir::OwningOpRef<mlir::ModuleOp> sourceSnapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> candidateSnapshot() const;
  llvm::StringRef role() const { return selectedRole; }
};
/// Source must already have passed complete construction/paired-role checking
/// and buildClosedExecutionPipeline. This operation admits the entire closed
/// Exec source before slicing. It performs no scoped expansion or CPU
/// selection.
llvm::Expected<CheckedEndpoint> closeEndpoint(mlir::ModuleOp source,
                                              llvm::StringRef role);
/// Read both actual subjects afresh. Check exact selected-role pruning,
/// nested-symbol dependency closure, unchanged bodies and retained attributes.
/// This structural check does not establish earlier source construction.
llvm::Error checkEndpointClosure(mlir::ModuleOp source,
                                 mlir::ModuleOp candidate,
                                 llvm::StringRef role);
/// Textual/direct pipeline adapter for the same checked operation.
std::unique_ptr<mlir::Pass> createSelectEndpointPass(llvm::StringRef role = {});
} // namespace zkc
#endif
