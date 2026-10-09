#ifndef ZKC_DIALECT_CONSTRAINTS
#define ZKC_DIALECT_CONSTRAINTS
include "mlir/IR/OpBase.td"
// Shared constraint for consumer dialects; does not redeclare core definitions.
// Logical interactive values; domains and exact kernel ports are verified on SSA.
// Role membership is explicit and independent of adapter coverage. Keep the
// broad RankedTensor carrier: exact tensor admission belongs to the verifier.
def Zkc_ProtocolData : Type<CPred<"::zkc::detail::isLogicalKernelData($_self)">,
  "logical protocol data or capability">;
#endif
