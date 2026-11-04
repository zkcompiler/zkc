#ifndef ZKC_COMPILER_COMPONENTCONTRACTS_H
#define ZKC_COMPILER_COMPONENTCONTRACTS_H
#include "mlir/IR/Attributes.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
namespace zkc::protocol {
struct SourceView;
struct SourceAllowance;
} // namespace zkc::protocol
namespace zkc::language {
/// Intern a semantic static term, ignoring optional StringAttr types. Expanded
/// nodes and string bytes share the caller's allowance; no wire tree is built.
llvm::Expected<mlir::Attribute> canonicalDeclarationTerm(mlir::Attribute,
                                                         uint64_t &remaining);
/// Derive occurrence-local proposals and routes from the admitted original
/// MLIR and its native closed-region view. These attachments carry no
/// mathematical or security evidence.
llvm::Expected<llvm::json::Object>
deriveComponentContracts(const protocol::SourceView &source);
llvm::Error checkComponentContracts(const protocol::SourceView &source,
                                    const llvm::json::Object &actual);
llvm::Error checkComponentDeclarations(const llvm::json::Value &declarations);
/// Native declaration semantics borrow actual attributes and spend the
/// subject's allowance; publication-only widths are enforced by the encoder.
llvm::Error checkComponentDeclarations(mlir::Attribute,
                                       protocol::SourceAllowance &);
} // namespace zkc::language
#endif
