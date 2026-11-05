#ifndef ZKC_TARGET_EVM_CURVE_H
#define ZKC_TARGET_EVM_CURVE_H

#include "zkc/Compiler/Evm.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "llvm/ADT/APInt.h"
#include <string>

namespace zkc::evm {
/// The one supported curve adapter. Installed nominal ScalarAction/Scalar and
/// codec facts are checked, not inferred from a CPU representation. The fixed
/// EIP-2537 curve equation and native compressed encoding are adapter premises;
/// the catalog does not declare a general 381-bit field arithmetic law.
struct GroupLayout {
  algebra::GroupType type;
  algebra::FieldType scalar;
  llvm::APInt scalarModulus{256, 0};
  llvm::APInt baseModulus{384, 0};
  unsigned frameTag = 0;
  static constexpr unsigned compressedBytes = 48;
  static constexpr unsigned affineBytes = 128;
};
llvm::Expected<GroupLayout> realizeGroup(algebra::GroupType);
/// Explicit target adapter support; group codecs also require this fork even
/// when the endpoint never performs an arithmetic operation on a group.
llvm::Error verifyGroupFork(EvmFork);

namespace detail {
/// Ordinary Yul helpers shared by production WireGenerator and the exporter.
/// No dynamic address, interpreter or source-name dispatch is exposed.
std::string curveHelpers();
} // namespace detail
} // namespace zkc::evm
#endif
