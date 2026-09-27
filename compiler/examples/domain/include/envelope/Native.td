#ifndef EXAMPLE_ENVELOPE_NATIVE
#define EXAMPLE_ENVELOPE_NATIVE
include "zkc/Dialect/IR.td"
include "zkc/Dialect/TypeBindings.td"
include "envelope/Declarations.td"
def EnvelopeDialect : ZKCDialect {
  let name = "envelope";
  let cppNamespace = "::envelope";
  let useDefaultTypePrinterParser = 1;
}
include "envelope/Specialization.td"

def Envelope : TypeDef<EnvelopeDialect, "Envelope"> {
  let mnemonic = "value";
  let parameters = (ins "::mlir::Type":$elementType, "uint64_t":$length);
  let assemblyFormat = "`<` $elementType `,` $length `>`";
}
def KeepOp : KernelOp<EnvelopeDialect, "keep", [EnvelopeKeep]> {
  // This domain's carrier is intentionally outside the base coarse type list.
  // The shared logical verifier still checks exact admitted signatures.
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site,
    ArrayAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<AnyType>:$outputs);
}
def EnvelopeAdapters : ZKC_TypeAdapterOwner<"envelope", "adapters">;
def EnvelopeBinding : ZKC_DirectBinding<EnvelopeValue, Envelope,
  "EnvelopeAdapter", EnvelopeAdapters>;
#endif
