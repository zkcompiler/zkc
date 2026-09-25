include "mlir/IR/OpBase.td"
def DiagonalProducerInterface : OpInterface<"DiagonalProducerInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Optional installed immutable depth-one diagonal representation for a logical map. All result uses must admit the same representation locally.}];
  let methods = [InterfaceMethod<"Return an available physical producer choice, or none",
    "std::optional<::zkc::DiagonalProducerSelection>", "getDiagonalProducerSelection">];
}
def DiagonalContractionInterface : OpInterface<"DiagonalContractionInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Optional installed contraction over a depth-one diagonal values operand.}];
  let methods = [InterfaceMethod<"Return an available physical contraction choice, or none",
    "std::optional<::zkc::DiagonalContractionSelection>", "getDiagonalContractionSelection">];
}
