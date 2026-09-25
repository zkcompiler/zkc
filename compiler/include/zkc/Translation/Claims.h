#ifndef ZKC_TRANSLATION_CLAIMS_H
#define ZKC_TRANSLATION_CLAIMS_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Claims/Claims.h"
namespace zkc::claims {
/// Registered, inspectable analysis IR, separate from executable PIR. Context
/// must outlive result. No API here erases or transforms executable checks.
/// Loads only the dialects used by the claim representation. Before reusing
/// the context for a protocol workflow (including checkConstruction), call
/// registerDialects and loadAllAvailableDialects as that workflow requires.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> import(const source::Module &,
                                                         const Contract &,
                                                         const Certificate &,
                                                         mlir::MLIRContext &);
/// Check in the candidate context without loading extra dialects. A valid
/// candidate already carries the dialects required by its subject types.
llvm::Error checkIR(const source::Module &, const Contract &, mlir::ModuleOp);
} // namespace zkc::claims
#endif
