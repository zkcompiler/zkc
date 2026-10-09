#ifndef ZKC_COMPILER_INTERNAL_LANGUAGEINTERFACE_H
#define ZKC_COMPILER_INTERNAL_LANGUAGEINTERFACE_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "llvm/Support/JSON.h"
namespace zkc::language {
class CheckedOriginal;
}
namespace zkc::language::detail {
llvm::Expected<std::string> emitInterface(const ClosedEntry &,
                                          llvm::StringRef original,
                                          llvm::StringRef toolchain,
                                          const Limits &);
/// The caller has verified this exact original module and computed its digest.
llvm::Expected<LanguageInterface>
decodeInterface(mlir::ModuleOp, llvm::StringRef digest,
                const llvm::json::Value &, const Limits &,
                llvm::ArrayRef<RelationAsset> = {});
llvm::Error withInterface(
    llvm::StringRef original, llvm::StringRef interface, const Limits &,
    llvm::ArrayRef<RelationAsset>,
    llvm::function_ref<llvm::Error(mlir::ModuleOp, LanguageInterface &&)>);
/// Reuse admitted immutable metadata; tighter limits take the byte-admission
/// path.
llvm::Error withInterface(
    const CheckedOriginal &, const Limits &,
    llvm::function_ref<llvm::Error(mlir::ModuleOp, const LanguageInterface &)>);
llvm::Expected<llvm::json::Value> parseInterface(llvm::StringRef,
                                                 const Limits &);
} // namespace zkc::language::detail
#endif
