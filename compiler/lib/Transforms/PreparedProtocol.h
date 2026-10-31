#ifndef ZKC_TRANSFORMS_PREPARED_PROTOCOL_H
#define ZKC_TRANSFORMS_PREPARED_PROTOCOL_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/Mathematical.h"
#include <optional>

namespace zkc::mathematical {
struct RealizationTrace;
// Private construction authority, valid only while its MLIR context lives.
// No mutable operation view escapes: snapshots are independent clones, and
// projection consumes the owned prepared subject. Public passes admit their
// own caller input instead of accepting a claim of prior preparation.
class PreparedProtocol {
  friend class RealizedProtocol;
  mlir::OwningOpRef<mlir::ModuleOp> original, module;
  MathematicalSelectionPolicy policy;
  PreparedProtocol(mlir::OwningOpRef<mlir::ModuleOp> original,
                   mlir::OwningOpRef<mlir::ModuleOp> module,
                   MathematicalSelectionPolicy policy)
      : original(std::move(original)), module(std::move(module)),
        policy(policy) {}
  static mlir::OwningOpRef<mlir::ModuleOp>
  projectOwned(mlir::OwningOpRef<mlir::ModuleOp>, bool simplify,
               MathematicalSelectionPolicy);

public:
  static std::optional<PreparedProtocol>
  prepare(mlir::ModuleOp source, MathematicalSelectionPolicy policy = {},
          RealizationTrace *trace = nullptr,
          llvm::ArrayRef<ApplicationStart> starts = {});
  // Independently resolve the complete selected construction closure against
  // the retained authored source. Consume only its unchanged prepared records
  // after admitting a scratch copy. Failure leaves this owner unchanged.
  mlir::LogicalResult consumeConstruction(llvm::StringRef selected);
  // Select explicit deployment roots after complete source admission and
  // checked expansion. Retain the full authored source. Other declarations
  // remain intact; any live reference to an omitted program is a refusal.
  // Failure leaves this owner unchanged.
  mlir::LogicalResult selectEntries(llvm::ArrayRef<llvm::StringRef> entries);
  mlir::OwningOpRef<mlir::ModuleOp> snapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> originalSnapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> project(bool simplify) &&;
  // Role-free helpers have no participant projection. Admit their closed
  // declaration inventory, expand scoped calls with the independent checker,
  // and change only the profile before shared numerical/physical selection.
  mlir::OwningOpRef<mlir::ModuleOp> execute() &&;
};
} // namespace zkc::mathematical
#endif
