#ifndef ZKC_DIALECT_CONSTRAINTS
#define ZKC_DIALECT_CONSTRAINTS
include "mlir/IR/OpBase.td"
// Shared constraint for consumer dialects; does not redeclare core definitions.
def Zkc_Flow : Type<CPred<"::llvm::isa<::zkc::FlowType>($_self)">,
                    "protocol ordering value">;
// Logical interactive values; domains and exact kernel ports are verified on SSA.
// Role membership is explicit and independent of adapter coverage. Keep the
// broad RankedTensor carrier: exact tensor admission belongs to the verifier.
defvar Zkc_KernelDataHeads = [
  "::zkc::FieldType", "::zkc::MultilinearType", "::zkc::QuadraticType",
  "::zkc::PointType", "::zkc::GroupType", "::zkc::UnivariateType",
  "::zkc::MatrixType", "::zkc::FixedVectorType", "::mlir::RankedTensorType",
  "::zkc::ObjectType", "::zkc::OracleObjectType", "::zkc::CapabilityType"
];
def Zkc_ProtocolData : Type<CPred<!strconcat(
  "::llvm::isa<", !interleave(Zkc_KernelDataHeads, ", "),
  ">($_self) || $_self.isSignlessInteger(1) || $_self.isUnsignedInteger(64)")>,
  "logical protocol data or capability">;
#endif
