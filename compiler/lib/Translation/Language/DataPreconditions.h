#ifndef ZKC_TRANSLATION_LANGUAGE_DATAPRECONDITIONS_H
#define ZKC_TRANSLATION_LANGUAGE_DATAPRECONDITIONS_H
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Operation.h"
#include "zkc/Language/Layout.h"
namespace zkc::language {
struct NativeDataPrecondition {
  DataPrecondition::Kind kind;
  unsigned left, right, leftAxis, rightAxis;
};
/// Logical product selectors become individual ABI arguments here. This is
/// representation mapping; semantic discharge belongs to Language/Analysis.
llvm::Expected<std::vector<NativeDataPrecondition>>
flattenDataPreconditions(const Declaration &, Layouts &);
mlir::ArrayAttr emitDataPreconditions(mlir::MLIRContext *,
                                      llvm::ArrayRef<NativeDataPrecondition>);
bool compareDataPreconditions(mlir::Operation &,
                              llvm::ArrayRef<NativeDataPrecondition>);
} // namespace zkc::language
#endif
