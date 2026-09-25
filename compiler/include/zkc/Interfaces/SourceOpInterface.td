include "mlir/IR/OpBase.td"
def SourceOpInterface : OpInterface<"SourceOpInterface"> {
  let cppNamespace = "::zkc";
  let description = [{Export the actual interpreted operation descriptor.}];
  let methods = [InterfaceMethod<"Return the resolved source descriptor",
                                 "llvm::json::Value", "getSourceDescriptor">];
}
