#ifndef ZKC_TRANSLATION_RELATIONS_H
#define ZKC_TRANSLATION_RELATIONS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Relation/IR/Assets.h"

namespace mlir {
class Builder;
}
namespace zkc::relation {
/// Relation imports load their owning zkc::relation::RelationDialect into the
/// supplied context.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importR1CS(const R1CS &, llvm::StringRef symbol, mlir::MLIRContext &);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importAIR(const AIR &, llvm::StringRef symbol, mlir::MLIRContext &);
/// Bounded public-assignment reference client: at most 8 rows, 128 columns,
/// 1024 nonzero terms, bls12-381.fr. Creates recipe, reduction, terminal,
/// composed main and independent exact-evaluation entries. Requires the
/// registered mathematical interfaces, as for native protocol compilation.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
authorR1CSSumcheck(const R1CS &, mlir::MLIRContext &);
/// Requirements retain the external canonical relation, never candidate IR.
/// The same authoring envelope is enforced by the correspondence checker.
llvm::json::Value r1csSumcheckRequirements(const R1CS &);
} // namespace zkc::relation

#endif
