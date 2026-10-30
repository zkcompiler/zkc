include "mlir/IR/OpBase.td"
def DiagonalProducerInterface : OpInterface<"DiagonalProducerInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Logical input and outcome-payload roles of a pointwise scalar action, excluding scope and outcome wrappers. Availability of a physical realization is a Target decision.}];
  let methods = [InterfaceMethod<"Return semantic producer roles, or none",
    "std::optional<::zkc::DiagonalProducerRoles>", "getDiagonalProducerRoles">];
}
def DiagonalContractionInterface : OpInterface<"DiagonalContractionInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Logical coefficient and values input roles of a linear contraction, excluding the scope operand. No representation or implementation is selected.}];
  let methods = [InterfaceMethod<"Return semantic contraction roles, or none",
    "std::optional<::zkc::DiagonalContractionRoles>", "getDiagonalContractionRoles">];
}
