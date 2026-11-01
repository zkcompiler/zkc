#ifndef ZKC_TARGET_EVM_ARITHMETIC_H
#define ZKC_TARGET_EVM_ARITHMETIC_H
#include "zkc/Compiler/Evm.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Target/Evm/Layout.h"
#include <memory>
namespace zkc::evm::detail {
/// Layout-sensitive field/vector helpers. Calls use the expanded checked-op
/// operands and results. Private identities derive from exact layouts.
class Arithmetic {
public:
  Arithmetic(NativeLayouts &, const EvmLimits &);
  ~Arithmetic();
  llvm::Expected<std::string> helper(CheckedOp);
  std::string helpers() const;

private:
  struct Storage;
  std::unique_ptr<Storage> storage;
};
} // namespace zkc::evm::detail
#endif
