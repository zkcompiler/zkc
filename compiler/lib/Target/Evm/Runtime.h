#ifndef ZKC_TARGET_EVM_RUNTIME_H
#define ZKC_TARGET_EVM_RUNTIME_H
#include "zkc/Compiler/Evm.h"
namespace zkc::evm::detail {
/// Checked ordinary Yul helper definitions, parameterized only by frozen
/// limits.
std::string runtimeHelpers(const EvmLimits &);
} // namespace zkc::evm::detail
#endif
