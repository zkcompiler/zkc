#ifndef ZKC_TRANSLATION_CLAIMS_H
#define ZKC_TRANSLATION_CLAIMS_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Claims/Claims.h"
namespace zkc::claims {
/// Registered, inspectable analysis IR, separate from executable PIR. Context
/// must outlive result. No API here erases or transforms executable checks.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> import(const source::Module &,
                                                         const Contract &,
                                                         const Certificate &,
                                                         mlir::MLIRContext &);
llvm::Error checkIR(const source::Module &, const Contract &, mlir::ModuleOp);
} // namespace zkc::claims
#endif
