#ifndef ZKC_TARGET_EVM_RUNTIME_H
#define ZKC_TARGET_EVM_RUNTIME_H
#include "zkc/Compiler/Evm.h"
#include "llvm/ADT/APInt.h"
namespace zkc::evm::detail {
/// Checked ordinary Yul helper definitions, parameterized by frozen limits.
/// With the challenge field modulus of a realized transcript suite, they
/// include exact hash-chain requests, challenge decoders and index checks.
/// Native numerical work budgets remain separate from EVM gas and ceilings.
std::string runtimeHelpers(const EvmLimits &,
                           const llvm::APInt *challengeModulus);
} // namespace zkc::evm::detail
#endif
