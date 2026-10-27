#ifndef ZKC_TRANSLATION_PACKING_H
#define ZKC_TRANSLATION_PACKING_H
#include "mlir/IR/Builders.h"
#include "zkc/Language/Layout.h"
namespace zkc::language {
/// Adapt an already checked value between its ordinary ABI and one contextual
/// mathematical carrier using data.make and ordered data.get projections.
/// These functions do not confer source access authority. Ordered execution
/// uses scoped variant/match construction instead. The caller owns operation
/// accounting (pack: product ? 1 : 0; unpack: product ? flat leaf count : 0).
llvm::Expected<mlir::Value> emitMathematicalPack(mlir::OpBuilder &,
                                                 mlir::Location,
                                                 const PackedLayout &,
                                                 mlir::ValueRange);
llvm::Expected<llvm::SmallVector<mlir::Value>>
emitMathematicalUnpack(mlir::OpBuilder &, mlir::Location, const PackedLayout &,
                       mlir::Value);
} // namespace zkc::language
#endif
