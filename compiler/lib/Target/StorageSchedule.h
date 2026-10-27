#ifndef ZKC_TARGET_STORAGE_SCHEDULE_H
#define ZKC_TARGET_STORAGE_SCHEDULE_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include <cstddef>
#include <tuple>

namespace zkc::target {
struct OperationDecision;

/// Coordinates in the retained selected executable subject. Payload outputs
/// use the semantic instruction even when the actual SSA value is a CFG block
/// argument. Body arguments use their owning function or protocol operation
/// and logical body index, excluding scope. Conversion results use their
/// consumer and conversion occurrence index.
struct StorageValue {
  enum Kind : unsigned {
    OperationResult,
    BlockArgument,
    ConversionResult
  } kind;
  size_t operation;
  unsigned index = 0;
  unsigned block = 0;
  auto key() const { return std::make_tuple(kind, operation, index, block); }
  bool operator==(const StorageValue &other) const {
    return key() == other.key();
  }
  bool operator<(const StorageValue &other) const {
    return key() < other.key();
  }
};
struct StoragePoint {
  enum Kind : unsigned { BlockEntry, AfterConversion, AfterOperation } kind;
  size_t operation;
  // Logical body index or conversion index; zero for AfterOperation.
  unsigned index = 0;
  auto key() const { return std::make_tuple(kind, operation, index); }
  bool operator==(const StoragePoint &other) const {
    return key() == other.key();
  }
  bool operator<(const StoragePoint &other) const {
    return key() < other.key();
  }
};
struct StorageRelease {
  StoragePoint point;
  llvm::SmallVector<StorageValue> values;
  bool operator==(const StorageRelease &other) const {
    return point == other.point && values == other.values;
  }
};

/// These functions borrow actual scoped bodies and physical ports/conversions;
/// they do not own another program model. Lifetime validation requires the
/// caller to validate supplied port/conversion decisions first.
/// Empty ports mean the source is already physical (the standalone transform).
llvm::Expected<llvm::SmallVector<StorageRelease>>
proposeStorage(mlir::ModuleOp, llvm::ArrayRef<OperationDecision> ports = {},
               mlir::Location *failureLocation = nullptr);
llvm::Error validateStorage(mlir::ModuleOp,
                            llvm::ArrayRef<OperationDecision> ports,
                            llvm::ArrayRef<StorageRelease>,
                            mlir::Location *failureLocation = nullptr);
} // namespace zkc::target
#endif
