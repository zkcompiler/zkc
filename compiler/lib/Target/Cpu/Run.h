#ifndef ZKC_TARGET_CPU_RUN_H
#define ZKC_TARGET_CPU_RUN_H
#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/Error.h"
namespace zkc::mathematical {
class RealizedProtocol;
}
namespace zkc::detail {
/// The prepared source remains alive through publication so source ordering
/// and role coordinates are checked independently of projection metadata.
llvm::Expected<std::string> buildRunBundle(mlir::ModuleOp prepared,
                                           mlir::ModuleOp physical,
                                           llvm::StringRef entry);
llvm::Error verifyRunBundle(mlir::ModuleOp prepared, mlir::ModuleOp physical,
                            llvm::StringRef bytes, llvm::StringRef entry);
// Retain the immutable checked common association through scheduling. The raw
// module overloads above remain strict and grant no authority to snapshots.
llvm::Expected<std::string>
buildRunBundle(const mathematical::RealizedProtocol &, mlir::ModuleOp physical,
               llvm::StringRef entry);
llvm::Error verifyRunBundle(const mathematical::RealizedProtocol &,
                            mlir::ModuleOp physical, llvm::StringRef bytes,
                            llvm::StringRef entry);
} // namespace zkc::detail
#endif
