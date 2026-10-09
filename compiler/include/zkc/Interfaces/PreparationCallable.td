#ifndef ZKC_INTERFACES_PREPARATION_CALLABLE_TD
#define ZKC_INTERFACES_PREPARATION_CALLABLE_TD

include "mlir/IR/OpBase.td"

def PreparationCallableOpInterface : OpInterface<"PreparationCallableOpInterface"> {
  let cppNamespace = "::zkc";
  let description = [{
    A symbol that local.apply may name before preparation replaces it with an
    ordinary local.func of the same signature. The owning dialect keeps the
    meaning and validation of the declaration; Local only reads the signature.
    Implementing this interface grants no profile admission: a closed profile
    names every admitted declaration operation explicitly.
  }];
  let methods = [
    InterfaceMethod<"Declared callable signature, or null when malformed. "
      "Symbol-use verification can run before the declaration's own verifier.",
      "::mlir::FunctionType", "getPreparationSignature", (ins), [{}], [{
        auto attribute =
            $_op->template getAttrOfType<::mlir::TypeAttr>("function_type");
        return attribute
                   ? ::llvm::dyn_cast<::mlir::FunctionType>(attribute.getValue())
                   : ::mlir::FunctionType();
      }]>
  ];
}

#endif
