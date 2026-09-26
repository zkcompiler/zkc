#ifndef ZKC_TRANSLATION_RELATIONS_H
#define ZKC_TRANSLATION_RELATIONS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"

namespace mlir {
class Builder;
}
namespace zkc::relation {
/// Encode canonical common-model constraint rows for relation.r1cs.
mlir::ArrayAttr encodeR1CSConstraints(mlir::Builder &, const R1CS &);
/// Relation imports load their owning RelationDialect into the supplied
/// context.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importR1CS(const R1CS &, llvm::StringRef symbol, mlir::MLIRContext &);
llvm::Expected<R1CS> readR1CSOperation(mlir::Operation *);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importAIR(const AIR &, llvm::StringRef symbol, mlir::MLIRContext &);
llvm::Expected<AIR> readAIROperation(mlir::Operation *);
} // namespace zkc::relation

#endif
