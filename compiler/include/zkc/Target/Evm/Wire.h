#ifndef ZKC_TARGET_EVM_WIRE_H
#define ZKC_TARGET_EVM_WIRE_H

#include "zkc/Compiler/Evm.h"
#include "zkc/Target/Evm/Layout.h"
#include <memory>

namespace zkc::evm {
class CheckedOp;

/// Complete native wire permission and concrete expected-type codec admission.
/// This is independent of local copyable representation. Checks every child,
/// including inactive alternatives and the element of an empty sequence.
llvm::Error verifyWireType(NativeLayouts &, mlir::Type);

/// Generates bounded canonical codecs and immutable structural operations.
/// All storage, lanes and field arithmetic facts belong to NativeLayouts.
class WireGenerator {
public:
  WireGenerator(NativeLayouts &, const EvmLimits &);
  ~WireGenerator();
  llvm::Expected<std::string> decoder(mlir::Type);
  llvm::Expected<std::string> encoder(mlir::Type);
  llvm::Expected<std::string> operation(CheckedOp);
  std::string definitions() const;

private:
  struct Storage;
  std::unique_ptr<Storage> storage;
};
} // namespace zkc::evm
#endif
