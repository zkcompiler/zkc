#ifndef ZKC_DIALECT_KERNELS_TD
#define ZKC_DIALECT_KERNELS_TD

include "zkc/Dialect/Constraints.td"
include "zkc/Contracts/Declarations.td"
include "zkc/Interfaces/LinearContraction.td"

class KernelOp<Dialect dialect, string name, list<ZKC_Operation> declarations,
               list<Trait> traits = []>
    : Op<dialect, name, traits>, ZKC_ContractMapping {
  let contracts = declarations;
  let arguments = (ins Variadic<Zkc_ProtocolData>:$inputs, StrAttr:$site,
    ArrayAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<Zkc_ProtocolData>:$outputs);
  let hasVerifier = 1;
  let extraClassDefinition = [{
    ::llvm::LogicalResult $cppClass::verify() {
      return ::zkc::detail::verifyLogicalKernel(getOperation());
    }
  }];
}

#endif
