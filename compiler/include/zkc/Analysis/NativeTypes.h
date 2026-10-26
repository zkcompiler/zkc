#ifndef ZKC_ANALYSIS_NATIVETYPES_H
#define ZKC_ANALYSIS_NATIVETYPES_H
#include "mlir/IR/Types.h"
#include "zkc/Contracts/NativePolicy.h"
#include "llvm/ADT/DenseMap.h"
#include <optional>
namespace mlir {
class Operation;
}
namespace zkc::mathematical {
using NativeTypePolicy = protocol::NativeTypePolicy;
/// Mathematical descriptors cannot cross executable ports or messages.
bool isFormalType(mlir::Type type);
// Closed native-local/0 vocabulary. Nominal formation is checked before any
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
// Total mathematical data excludes authority and mutable service resources.
mlir::LogicalResult verifyTotalTypes(mlir::Operation *operation,
                                     NativeTypePolicies &types);
} // namespace zkc::mathematical
#endif
