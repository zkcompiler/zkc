#ifndef ZKC_ANALYSIS_RESIDUETILE_H
#define ZKC_ANALYSIS_RESIDUETILE_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/ArrayRef.h"
#include <cstdint>
#include <optional>

namespace zkc::residue {
/// An owned interpretation, never approval of a subsequently mutable packet.
/// `scalar` is reconstructed from actual word operations after independent
/// source correspondence. The storage count describes canonical word buffers,
/// not resident provider bytes or a runtime allocation grant.
struct Tile {
  mlir::OwningOpRef<mlir::ModuleOp> scalar;
  unsigned lanes;
  uint64_t peakPrivateBytes;
};

/// Check a complete static pointwise Vector/MemRef candidate, including unused
/// operations, exact accesses, private owners, initialization and release.
/// Borrowed tiles are read-only; exactly one fresh initialized owner is
/// returned. Poison is allowed only as padding in independently proven
/// full-tile reads. Reconstruct the actual scalar word expression and compare
/// it with source.
std::optional<Tile> readTile(mlir::ModuleOp source,
                             llvm::ArrayRef<bool> rowwise,
                             mlir::ModuleOp candidate);
} // namespace zkc::residue
#endif
