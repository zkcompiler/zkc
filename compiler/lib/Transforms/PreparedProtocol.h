#ifndef ZKC_TRANSFORMS_PREPARED_PROTOCOL_H
#define ZKC_TRANSFORMS_PREPARED_PROTOCOL_H

#include "mlir/IR/BuiltinOps.h"
#include <optional>

namespace zkc::mathematical {
// Private construction authority, valid only while its MLIR context lives.
// No mutable operation view escapes: snapshots are independent clones, and
// projection consumes the owned prepared subject. Public passes admit their
// own caller input instead of accepting a claim of prior preparation.
class PreparedProtocol {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  explicit PreparedProtocol(mlir::OwningOpRef<mlir::ModuleOp> module)
      : module(std::move(module)) {}

public:
  static std::optional<PreparedProtocol> prepare(mlir::ModuleOp source);
  mlir::OwningOpRef<mlir::ModuleOp> snapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> project(bool simplify) &&;
};
} // namespace zkc::mathematical
#endif
