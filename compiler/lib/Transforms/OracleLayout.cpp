#include "OracleLayout.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::protocol {
Expected<OracleTableLayout>
OracleTableLayout::create(uint64_t rows, OracleLeafGrouping grouping,
                          OracleLeafOrder order) {
  if (!rows || (rows & (rows - 1)))
    return error("oracle-layout-shape");
  if ((grouping != OracleLeafGrouping::Individual &&
       grouping != OracleLeafGrouping::AntipodalPairs) ||
      (order != OracleLeafOrder::Natural &&
       order != OracleLeafOrder::BitReversed))
    return error("oracle-layout-kind");
  if (grouping == OracleLeafGrouping::AntipodalPairs && rows < 2)
    return error("oracle-layout-pair");
  return OracleTableLayout(rows, grouping, order);
}
uint64_t OracleTableLayout::permute(uint64_t leaf) const {
  if (order == OracleLeafOrder::Natural)
    return leaf;
  uint64_t reversed = 0;
  // At most 63 bits. The singleton has zero bits and maps to itself.
  for (uint64_t count = leaves(); count > 1; count >>= 1) {
    reversed = (reversed << 1) | (leaf & 1);
    leaf >>= 1;
  }
  return reversed;
}
Expected<OracleLeafPosition>
OracleTableLayout::locate(uint64_t logicalRow) const {
  if (logicalRow >= rows())
    return error("oracle-layout-position");
  const uint64_t count = leaves();
  return OracleLeafPosition{permute(logicalRow % count),
                            unsigned(logicalRow / count)};
}
Expected<uint64_t>
OracleTableLayout::logicalRow(OracleLeafPosition position) const {
  if (position.leaf >= leaves() || position.slot >= width())
    return error("oracle-layout-position");
  // The permutation is involutive; the maximum is rows - 1, without overflow.
  return permute(position.leaf) + uint64_t(position.slot) * leaves();
}
} // namespace zkc::protocol
