#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_TD
include "zkc/Dialect/Runtime/IR/RuntimeTypes.td"
include "zkc/Dialect/BoundOperations.td"
def PrepareQuotientMatrixOp : BoundOp<RuntimeDialect, "prepare_quotient_matrix", [OpQuotientPrepareMatrix]>;
def QuotientMatvecOp : BoundOp<RuntimeDialect, "quotient_matvec", [OpQuotientMatvec]>;
#endif
