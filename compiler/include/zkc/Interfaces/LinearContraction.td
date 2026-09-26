include "mlir/IR/OpBase.td"
def DiagonalProducerInterface : OpInterface<"DiagonalProducerInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Logical operand and result roles of a pointwise scalar action. Availability of a physical realization is a Target decision.}];
  let methods = [InterfaceMethod<"Return semantic producer roles, or none",
    "std::optional<::zkc::DiagonalProducerRoles>", "getDiagonalProducerRoles">];
}
def DiagonalContractionInterface : OpInterface<"DiagonalContractionInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Logical coefficient and values roles of a linear contraction. No representation or implementation is selected.}];
  let methods = [InterfaceMethod<"Return semantic contraction roles, or none",
    "std::optional<::zkc::DiagonalContractionRoles>", "getDiagonalContractionRoles">];
}
