#ifndef ZKC_TARGET_EVM_AUTHENTICATION_H
#define ZKC_TARGET_EVM_AUTHENTICATION_H
#include "zkc/Target/Evm/Layout.h"
#include <string>
namespace zkc::evm {
struct KeccakRows {
  const FieldLayout *field;
  std::string codec;
  unsigned rootTag, pathTag;
};
/// Realize installed Keccak row facts; this grants no oracle controller
/// meaning.
llvm::Expected<KeccakRows> realizeKeccakRows(NativeLayouts &, mlir::Type root);
} // namespace zkc::evm
#endif
