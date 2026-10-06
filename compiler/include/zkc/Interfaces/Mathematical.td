#ifndef ZKC_INTERFACES_MATHEMATICAL_TD
#define ZKC_INTERFACES_MATHEMATICAL_TD

include "mlir/IR/OpBase.td"

def MathematicalOpInterface : OpInterface<"MathematicalOpInterface"> {
  let cppNamespace = "::zkc";
  let description = [{
    Mathematical identity and the direct operand dependencies of each result.
    These are views of the current SSA operation, not stored graph nodes or
    execution recipes. Implementing this interface does not grant admission
    to any protocol profile, authorize a rewrite, or establish totality on
    unadmitted types. Clients first check the closed profile vocabulary.
    The native profile currently requires every operand in source order for
    each admitted result. Projection clones whole operations; a narrower
    dependency view needs a separately admitted decomposition before cloning.
  }];
  let methods = [
    InterfaceMethod<"Identity on this form, or none for an unsupported form",
      "std::optional<::zkc::MathematicalIdentity>", "getMathematicalIdentity">,
    InterfaceMethod<"Ordered, distinct operand indices required by a result",
      "::llvm::SmallVector<unsigned>", "getOperandDependencies",
      (ins "unsigned":$result)>
  ];
}

#endif
