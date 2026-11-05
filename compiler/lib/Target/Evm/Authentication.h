#ifndef ZKC_TARGET_EVM_DETAIL_AUTHENTICATION_H
#define ZKC_TARGET_EVM_DETAIL_AUTHENTICATION_H
#include "zkc/Compiler/Evm.h"
#include "zkc/Target/Evm/Authentication.h"
#include <map>
namespace zkc::evm::detail {
class Authentication {
public:
  Authentication(NativeLayouts &layouts, const EvmLimits &limits)
      : layouts(layouts), limits(limits) {}
  llvm::Expected<std::string> helper(mlir::Operation *);
  std::string helpers() const;

private:
  NativeLayouts &layouts;
  EvmLimits limits;
  std::map<std::string, std::string> definitions;
};
} // namespace zkc::evm::detail
#endif
