#include "zkc/Contracts/Operations.h"
#include "llvm/ADT/STLExtras.h"
namespace zkc {
#define ZKC_MATHEMATICAL_INTRINSICS
#include "zkc/Contracts/Mathematical.inc"
#undef ZKC_MATHEMATICAL_INTRINSICS
const MathematicalIntrinsic *mathematicalIntrinsic(llvm::StringRef name) {
  auto values = mathematicalIntrinsics();
  auto found = llvm::find_if(
      values, [&](const auto &value) { return value.name == name; });
  return found == values.end() ? nullptr : &*found;
}
} // namespace zkc

namespace zkc::protocol {
#define ZKC_MATHEMATICAL_LAWS
#include "zkc/Contracts/Mathematical.inc"
#undef ZKC_MATHEMATICAL_LAWS
} // namespace zkc::protocol
