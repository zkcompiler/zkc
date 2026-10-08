#ifndef ZKC_COMPILER_INTERNAL_LANGUAGEINTERFACE_H
#define ZKC_COMPILER_INTERNAL_LANGUAGEINTERFACE_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "llvm/Support/JSON.h"
namespace zkc::language::detail {
/// The caller has verified this exact original module and computed its digest.
llvm::Expected<LanguageInterface> readInterface(mlir::ModuleOp,
                                                llvm::StringRef digest,
                                                llvm::StringRef interface,
                                                const Limits &);
llvm::Expected<LanguageInterface> decodeInterface(mlir::ModuleOp,
                                                  llvm::StringRef digest,
                                                  const llvm::json::Value &,
                                                  const Limits &);
llvm::Expected<llvm::json::Value> parseInterface(llvm::StringRef,
                                                 const Limits &);
} // namespace zkc::language::detail
#endif
