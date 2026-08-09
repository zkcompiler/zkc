//===- PirDialect.td - Protocol IR dialect -----------------*- tablegen -*-===//
// pir: typed protocol objects (P_core / P_closed) per docs/spec/carrier.md.
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_PIR_DIALECT_TD
#define ZKC_DIALECT_PIR_DIALECT_TD

include "mlir/IR/OpBase.td"

def Pir_Dialect : Dialect {
  let name = "pir";
  let summary = "Protocol IR: typed protocol objects and transcript chains";
  let description = [{
    Carrier of protocol objects (docs/spec/carrier.md): an open protocol
    (`pir.protocol`) holds a linear chain of transcript events threaded by
    builtin `token` values; declared verifier checks read the events'
    value handles; a sealed protocol (`pir.sealed`) is an immutable,
    content-addressed artifact that is never rewritten.
  }];
  let cppNamespace = "::zkc::pir";
  let useDefaultTypePrinterParser = 1;
  let extraClassDeclaration = [{
    void registerTypes();
  }];
}

class Pir_Op<string mnemonic, list<Trait> traits = []>
    : Op<Pir_Dialect, mnemonic, traits>;

#endif // ZKC_DIALECT_PIR_DIALECT_TD
