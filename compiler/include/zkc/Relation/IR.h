#ifndef ZKC_RELATION_IR_H
#define ZKC_RELATION_IR_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"

namespace zkc::relation {
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importR1CS(const R1CS &, llvm::StringRef symbol, mlir::MLIRContext &);
llvm::Expected<R1CS> readR1CSOperation(mlir::Operation *);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importAIR(const AIR &, llvm::StringRef symbol, mlir::MLIRContext &);
llvm::Expected<AIR> readAIROperation(mlir::Operation *);
} // namespace zkc::relation

#endif
