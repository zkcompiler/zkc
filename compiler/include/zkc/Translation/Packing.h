#ifndef ZKC_TRANSLATION_PACKING_H
#define ZKC_TRANSLATION_PACKING_H
#include "mlir/IR/Builders.h"
#include "zkc/Language/Layout.h"
namespace zkc::language {
enum class PackingMode { Mathematical, Local };
/// Adapt an already checked value between its ordinary ABI and one contextual
/// native carrier. These functions do not confer source access authority.
/// Local unpack emits a single-arm match with an identity payload yield;
/// mathematical unpack emits ordered data.get projections. The caller owns
/// operation/work accounting (pack: product ? 1 : 0; unpack: local product ? 2
/// : mathematical product ? flat leaf count : 0).
llvm::Expected<mlir::Value> emitPack(mlir::OpBuilder &, mlir::Location,
                                     const PackedLayout &, mlir::ValueRange,
                                     PackingMode, llvm::StringRef site = {});
llvm::Expected<llvm::SmallVector<mlir::Value>>
emitUnpack(mlir::OpBuilder &, mlir::Location, const PackedLayout &, mlir::Value,
           PackingMode, llvm::StringRef site = {});
} // namespace zkc::language
#endif
