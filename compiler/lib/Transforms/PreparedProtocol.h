#ifndef ZKC_TRANSFORMS_PREPARED_PROTOCOL_H
#define ZKC_TRANSFORMS_PREPARED_PROTOCOL_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include <optional>

namespace zkc::mathematical {
struct RealizationTrace;
// Private construction authority, valid only while its MLIR context lives.
// No mutable operation view escapes: snapshots are independent clones, and
// projection consumes the owned prepared subject. Public passes admit their
// own caller input instead of accepting a claim of prior preparation.
class PreparedProtocol {
  friend class RealizedProtocol;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  explicit PreparedProtocol(mlir::OwningOpRef<mlir::ModuleOp> module)
      : module(std::move(module)) {}

public:
  static std::optional<PreparedProtocol>
  prepare(mlir::ModuleOp source, MathematicalSelectionPolicy policy = {},
          RealizationTrace *trace = nullptr);
  mlir::OwningOpRef<mlir::ModuleOp> snapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> project(bool simplify) &&;
  // Role-free helpers have no participant projection. Admit their closed
  // declaration inventory, expand scoped calls with the independent checker,
  // and change only the profile before shared numerical/physical selection.
  mlir::OwningOpRef<mlir::ModuleOp> execute() &&;
};
} // namespace zkc::mathematical
#endif
