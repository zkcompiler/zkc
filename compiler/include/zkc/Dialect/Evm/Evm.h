#ifndef ZKC_DIALECT_EVM_EVM_H
#define ZKC_DIALECT_EVM_EVM_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

namespace zkc::evm {
/// Integer words use builtin i256, predicates i1 and bounded addresses/counts
/// i64. A slice is an explicit (address, element-count) pair; checked
/// operations validate its bounds before accessing memory. No CPU
/// representation is used.
class EvmDialect final : public mlir::Dialect {
public:
  explicit EvmDialect(mlir::MLIRContext *);
  static llvm::StringRef getDialectNamespace() { return "evm"; }
};

/// Total, word-exact EVM arithmetic. The closed opcode inventory is addmod,
/// mulmod. Modulus is an explicit third i256 operand (zero follows EVM
/// semantics).
class WordOp final
    : public mlir::Op<WordOp, mlir::OpTrait::NOperands<3>::Impl,
                      mlir::OpTrait::OneResult, mlir::OpTrait::ZeroRegions,
                      mlir::MemoryEffectOpInterface::Trait> {
public:
  using Op::Op;
  static llvm::StringRef getOperationName() { return "evm.word"; }
  static llvm::ArrayRef<llvm::StringRef> getAttributeNames();
  static void build(mlir::OpBuilder &, mlir::OperationState &, llvm::StringRef,
                    mlir::Value, mlir::Value, mlir::Value);
  static WordOp create(mlir::OpBuilder &, mlir::Location, llvm::StringRef,
                       mlir::Value, mlir::Value, mlir::Value);
  llvm::StringRef opcode();
  mlir::LogicalResult verify();
  void
  getEffects(llvm::SmallVectorImpl<mlir::MemoryEffects::EffectInstance> &) {}
};

/// A checked EVM primitive, selected at compile time from a closed inventory.
/// All have ordered read/write effects, including transcript transitions whose
/// final digest is unused. They may revert and are never speculatable. The
/// exporter outlines their checked implementation into ordinary Yul helpers.
/// Layout-sensitive operations require an exact logical TypeAttr value_type;
/// NativeLayouts determines their expanded signature and collection stride.
/// Field/vector primitives belong to Arithmetic, immutable structural and
/// canonical wire primitives to Wire, and affine/control primitives to Runtime.
class CheckedOp final
    : public mlir::Op<CheckedOp, mlir::OpTrait::VariadicOperands,
                      mlir::OpTrait::VariadicResults,
                      mlir::OpTrait::ZeroRegions,
                      mlir::MemoryEffectOpInterface::Trait> {
public:
  using Op::Op;
  static llvm::StringRef getOperationName() { return "evm.checked"; }
  static llvm::ArrayRef<llvm::StringRef> getAttributeNames();
  static void build(mlir::OpBuilder &, mlir::OperationState &, mlir::TypeRange,
                    llvm::StringRef, mlir::ValueRange,
                    mlir::ArrayRef<mlir::NamedAttribute> = {});
  static CheckedOp create(mlir::OpBuilder &, mlir::Location, mlir::TypeRange,
                          llvm::StringRef, mlir::ValueRange,
                          mlir::ArrayRef<mlir::NamedAttribute> = {});
  llvm::StringRef opcode();
  mlir::LogicalResult verify();
  void getEffects(llvm::SmallVectorImpl<mlir::MemoryEffects::EffectInstance> &);
};
/// The same positive opcode inventory is used by dialect verification and Yul.
bool isCheckedOpcode(llvm::StringRef);
} // namespace zkc::evm
#endif
