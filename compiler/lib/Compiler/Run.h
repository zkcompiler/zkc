#ifndef ZKC_LIB_COMPILER_RUN_H
#define ZKC_LIB_COMPILER_RUN_H
#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/Error.h"
namespace zkc::detail {
/// The prepared source remains alive through publication so source ordering
/// and role coordinates are checked independently of projection metadata.
llvm::Expected<std::string> buildRunBundle(mlir::ModuleOp prepared,
                                           mlir::ModuleOp physical,
                                           llvm::StringRef entry);
llvm::Error verifyRunBundle(mlir::ModuleOp prepared, mlir::ModuleOp physical,
                            llvm::StringRef bytes, llvm::StringRef entry);
} // namespace zkc::detail
#endif
