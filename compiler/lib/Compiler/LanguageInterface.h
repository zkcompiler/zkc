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
llvm::Expected<LanguageInterface> decodeInterface(mlir::ModuleOp,
                                                  llvm::StringRef digest,
                                                  const llvm::json::Value &,
                                                  const Limits &,
                                                  llvm::ArrayRef<Asset> = {});
llvm::Error withInterface(
    llvm::StringRef original, llvm::StringRef interface, const Limits &,
    llvm::ArrayRef<Asset>,
    llvm::function_ref<llvm::Error(mlir::ModuleOp, LanguageInterface &&)>);
/// Reuse admitted immutable metadata; tighter limits take the byte-admission
/// path.
llvm::Error withInterface(
    const CheckedOriginal &, const Limits &,
    llvm::function_ref<llvm::Error(mlir::ModuleOp, const LanguageInterface &)>);
llvm::json::Value encodeInterfaceSchema(const InterfaceSchema &);
llvm::json::Value encodeInterfaceOracle(const InterfaceOracle &);
llvm::Expected<std::shared_ptr<const InterfaceSchema>>
decodeHostSchema(const llvm::json::Value &, const Limits &);
llvm::Expected<llvm::json::Value> parseInterface(llvm::StringRef,
                                                 const Limits &);
/// Common lexical bounds for interfaces and executable Host carriers. Embedded
/// program/package strings use the carrier ceiling instead of the metadata cap.
llvm::Expected<llvm::json::Value> parseEntryJson(llvm::StringRef,
                                                 size_t byteLimit,
                                                 size_t stringLimit,
                                                 llvm::StringRef invalidCode);
} // namespace zkc::language::detail
#endif
