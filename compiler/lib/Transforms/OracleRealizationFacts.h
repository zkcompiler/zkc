#ifndef ZKC_TRANSFORMS_ORACLEREALIZATIONFACTS_H
#define ZKC_TRANSFORMS_ORACLEREALIZATIONFACTS_H
#include "llvm/ADT/SmallVector.h"
#include <cstdint>
#include <optional>
#include <string>
#include <vector>
namespace mlir {
class Operation;
}
namespace zkc::protocol {
// Generated identifiers use the program grammar. Full source coordinates stay
// separate from their short spelling, for the eventual realization record.
struct OracleCommonOccurrence {
  std::string site, purpose, role;
  std::vector<unsigned> sourcePath;
};
struct OracleCommonQueryBlock {
  std::vector<std::vector<unsigned>> queries;
  // Dynamic packet bound; null for ideal local evaluation. Actual physical
  // groups are first-use runtime data checked by the packet reader.
  std::optional<uint64_t> packetCapacity;
};
struct OracleEntryFacts {
  std::string entry;
  std::vector<OracleCommonOccurrence> occurrences;
  std::vector<OracleCommonQueryBlock> queryBlocks;
};
// Derived by the independent actual-body reader, never from a wire record.
// Operation handles borrow the immutable candidate; mutation invalidates them.
struct OracleRealizationFacts {
  llvm::SmallVector<mlir::Operation *> openingRequests;
  std::vector<OracleEntryFacts> entries;
};
} // namespace zkc::protocol
#endif
