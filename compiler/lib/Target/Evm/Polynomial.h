#ifndef ZKC_TARGET_EVM_DETAIL_POLYNOMIAL_H
#define ZKC_TARGET_EVM_DETAIL_POLYNOMIAL_H
#include "zkc/Compiler/Evm.h"
#include "zkc/Target/Evm/Layout.h"
namespace zkc::evm::detail {
/// Definitions use Arithmetic's canonical coefficient and field helpers.
llvm::Expected<std::string> polynomialHelper(mlir::Operation *,
                                             const FieldLayout &,
                                             const EvmLimits &,
                                             llvm::StringRef name);
} // namespace zkc::evm::detail
#endif
