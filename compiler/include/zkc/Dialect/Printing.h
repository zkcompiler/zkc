#ifndef ZKC_DIALECT_PRINTING_H
#define ZKC_DIALECT_PRINTING_H
#include "mlir/IR/OperationSupport.h"
#include <limits>
namespace zkc {
/// Artifact printing is independent of process-global MLIR command-line flags.
/// Elision thresholds exceed every admitted payload; hex printing is disabled.
inline mlir::OpPrintingFlags canonicalPrintingFlags(bool localScope = false) {
  return mlir::OpPrintingFlags()
      .printGenericOpForm(true)
      .enableDebugInfo(false)
      .skipRegions(false)
      .assumeVerified(false)
      .useLocalScope(localScope)
      .printValueUsers(false)
      .printUniqueSSAIDs(false)
      .printNameLocAsPrefix(false)
      .elideLargeElementsAttrs(std::numeric_limits<int64_t>::max())
      .elideLargeResourceString(std::numeric_limits<int64_t>::max())
      .printLargeElementsAttrWithHex(-1);
}
} // namespace zkc
#endif
