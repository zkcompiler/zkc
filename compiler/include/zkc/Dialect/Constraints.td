#ifndef ZKC_DIALECT_CONSTRAINTS
#define ZKC_DIALECT_CONSTRAINTS
include "mlir/IR/OpBase.td"
// Shared constraint for consumer dialects; does not redeclare core definitions.
def Zkc_Flow : Type<CPred<"::llvm::isa<::zkc::FlowType>($_self)">,
                    "protocol ordering value">;
// Logical interactive values; domains and exact kernel ports are verified on SSA.
def Zkc_ProtocolData : Type<CPred<"::llvm::isa<::zkc::FieldType, ::zkc::MultilinearType, ::zkc::QuadraticType, ::zkc::PointType, ::zkc::GroupType, ::zkc::UnivariateType, ::zkc::MatrixType, ::mlir::RankedTensorType, ::zkc::ObjectType, ::zkc::OracleObjectType, ::zkc::CapabilityType>($_self) || $_self.isSignlessInteger(1) || $_self.isUnsignedInteger(64)">,
  "logical protocol data or capability">;
#endif
