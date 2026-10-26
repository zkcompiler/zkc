#ifndef ZKC_CONVERSION_STORAGE_H
#define ZKC_CONVERSION_STORAGE_H

#include "../Target/StorageSchedule.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <map>

namespace zkc::protocol {
/// Insert checked releases at semantic body points in the actual scoped CFG.
/// Does not select lifetimes or alter any payload or control-flow edge.
llvm::Error applyStorage(mlir::ModuleOp,
                         llvm::ArrayRef<target::StorageRelease>);

/// Compare complete physical subjects while reading only inserted releases.
/// Existing releases must keep their operands and computation positions.
llvm::Expected<llvm::SmallVector<target::StorageRelease>>
readStorageReleases(mlir::ModuleOp before, mlir::ModuleOp after);
llvm::Error
verifyStorageMaterialization(mlir::ModuleOp before, mlir::ModuleOp after,
                             llvm::ArrayRef<target::StorageRelease> releases);
} // namespace zkc::protocol
#endif
