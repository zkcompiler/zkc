#ifndef ZKC_DIALECT_PROTOCOL_NATIVEPOLICY_H
#define ZKC_DIALECT_PROTOCOL_NATIVEPOLICY_H
#include "mlir/IR/Types.h"
#include "llvm/ADT/DenseMap.h"
#include <optional>
namespace mlir {
class Operation;
}
namespace zkc::mathematical {
struct NativeTypePolicy {
  bool total;
  bool shared;
  bool affine;
  bool protocolPort;
  bool wire;
};
// Closed native-local/1 vocabulary. Nominal formation is checked before any
// use permission is returned; containers recursively check their leaves.
std::optional<NativeTypePolicy> nativeTypePolicy(mlir::Type type);
class NativeTypePolicies {
  mlir::Operation *owner;
  llvm::DenseMap<mlir::Type, std::optional<NativeTypePolicy>> cache;
  unsigned remaining = 200000;
  // Bytes of distinct top-level spellings, not a character-instruction budget.
  // Nested variant decoding can revisit a spelling at each formed type depth.
  size_t remainingBytes = 1024 * 1024;
  bool limited = false;

public:
  explicit NativeTypePolicies(mlir::Operation *owner) : owner(owner) {}
  std::optional<NativeTypePolicy> get(mlir::Type type);
};
mlir::LogicalResult verifyNativeLocals(mlir::Operation *unit, bool allowApply,
                                       NativeTypePolicies &types);
mlir::LogicalResult verifyNativeLocals(mlir::Operation *unit, bool allowApply);
mlir::LogicalResult verifyNativeExecution(mlir::Operation *unit);
mlir::LogicalResult verifyNativeExecution(mlir::Operation *unit,
                                          NativeTypePolicies &types);
mlir::LogicalResult verifyProjectionMetadata(mlir::Operation *unit,
                                             NativeTypePolicies &types);
} // namespace zkc::mathematical
#endif
