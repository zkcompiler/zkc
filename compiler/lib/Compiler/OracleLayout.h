#ifndef ZKC_COMPILER_ORACLELAYOUT_H
#define ZKC_COMPILER_ORACLELAYOUT_H
#include "llvm/Support/Error.h"
#include <cstdint>

namespace zkc::protocol {
enum class OracleLeafGrouping { Individual, AntipodalPairs };
enum class OracleLeafOrder { Natural, BitReversed };
struct OracleLeafPosition {
  uint64_t leaf;
  unsigned slot;
  bool operator==(const OracleLeafPosition &other) const {
    return leaf == other.leaf && slot == other.slot;
  }
};
/// Checked mathematical layout of a power-of-two table. An antipodal leaf
/// holds logical rows i and i + rows/2, in that order. Permutation applies to
/// leaf indices after grouping, never independently to the payload slots.
/// This fixes neither a cryptographic scheme nor a native representation.
class OracleTableLayout {
public:
  static llvm::Expected<OracleTableLayout>
  create(uint64_t rows, OracleLeafGrouping, OracleLeafOrder);
  uint64_t rows() const { return rowCount; }
  uint64_t leaves() const { return rowCount / width(); }
  unsigned width() const {
    return grouping == OracleLeafGrouping::Individual ? 1 : 2;
  }
  llvm::Expected<OracleLeafPosition> locate(uint64_t logicalRow) const;
  llvm::Expected<uint64_t> logicalRow(OracleLeafPosition) const;

private:
  OracleTableLayout(uint64_t rows, OracleLeafGrouping grouping,
                    OracleLeafOrder order)
      : rowCount(rows), grouping(grouping), order(order) {}
  uint64_t permute(uint64_t leaf) const;
  uint64_t rowCount;
  OracleLeafGrouping grouping;
  OracleLeafOrder order;
};
} // namespace zkc::protocol
#endif
