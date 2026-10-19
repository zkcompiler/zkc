#ifndef ZKC_CONVERSION_STORAGE_H
#define ZKC_CONVERSION_STORAGE_H

#include "../Target/StorageSchedule.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <map>

namespace zkc::protocol {
/// Map and insert only recorded decisions. Operations are the original subject
/// preorder with replaced operations updated in place; conversions are indexed
/// by their consumer and occurrence. No liveness analysis occurs here.
llvm::Error
applyStorage(mlir::ModuleOp, llvm::ArrayRef<target::StorageRelease>,
             llvm::ArrayRef<mlir::Operation *> operations,
             llvm::ArrayRef<llvm::SmallVector<mlir::Value>> conversions = {});

/// An output reader consumes exact chunks at exact points, including their
/// operand ordering. Unrecorded releases remain at the caller's cursor and
/// therefore fail ordinary operation correspondence.
class StorageReleaseReader {
  std::map<target::StoragePoint,
           llvm::SmallVector<const target::StorageRelease *>>
      points;
  size_t consumed = 0, expected = 0;

public:
  explicit StorageReleaseReader(llvm::ArrayRef<target::StorageRelease>);
  bool read(target::StoragePoint, mlir::Block &, mlir::Block::iterator &,
            llvm::function_ref<mlir::Value(target::StorageValue)>,
            size_t &remaining);
  bool complete() const { return consumed == expected; }
};

/// Compare complete physical subjects while reading only inserted releases.
/// Existing releases must keep their operands and computation positions.
llvm::Expected<llvm::SmallVector<target::StorageRelease>>
readStorageReleases(mlir::ModuleOp before, mlir::ModuleOp after);
llvm::Error
verifyStorageMaterialization(mlir::ModuleOp before, mlir::ModuleOp after,
                             llvm::ArrayRef<target::StorageRelease> releases);
} // namespace zkc::protocol
#endif
