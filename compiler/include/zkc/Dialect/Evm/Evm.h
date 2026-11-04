#ifndef ZKC_DIALECT_EVM_EVM_H
#define ZKC_DIALECT_EVM_EVM_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Runtime/IR/RuntimeAttrs.h"

namespace zkc::evm {
/// Physical lanes are builtin integers. Complete logical layouts and source
/// occurrence coordinates keep their common native owners.
class EvmDialect final : public mlir::Dialect {
public:
  explicit EvmDialect(mlir::MLIRContext *);
  static llvm::StringRef getDialectNamespace() { return "evm"; }
};
} // namespace zkc::evm

#define GET_OP_CLASSES
#include "zkc/Dialect/Evm/Ops.h.inc"
#endif
