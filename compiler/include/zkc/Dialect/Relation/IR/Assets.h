#ifndef ZKC_DIALECT_RELATION_IR_ASSETS_H
#define ZKC_DIALECT_RELATION_IR_ASSETS_H
#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
namespace mlir {
class Builder;
class Operation;
} // namespace mlir
namespace zkc::relation {
mlir::ArrayAttr encodeR1CSConstraints(mlir::Builder &, const R1CS &);
mlir::DictionaryAttr encodeAIRAttributes(mlir::Builder &, const AIR &);
llvm::Expected<R1CS> readR1CSOperation(mlir::Operation *);
llvm::Expected<AIR> readAIROperation(mlir::Operation *);
} // namespace zkc::relation
#endif
