//===- OirDialect.td - Operator-layer dialect ---------------*- tablegen -*-===//

#ifndef ZKC_DIALECT_OIR_DIALECT_TD
#define ZKC_DIALECT_OIR_DIALECT_TD

include "mlir/IR/OpBase.td"

def Oir_Dialect : Dialect {
  let name = "oir";
  let summary = "operator layer: endpoint programs with embedded provenance";
  let description = [{
    OIR carries the projected endpoint semantics of sealed PIR. The
    top-level carrier is an `oir.artifact`: one endpoint `oir.program`
    whose ops each embed their `src` provenance — the canonical event
    positions they cover — so the projection evidence travels in the
    ops and no pass can drop it silently. Route, ABI, and conformance
    facts are views over the artifact and its source, never
    materialized sections (docs/spec/boundaries.md §2).
  }];
  let cppNamespace = "::zkc::oir";
  let useDefaultTypePrinterParser = 1;
  let extraClassDeclaration = [{
    void registerTypes();
  }];
}

class Oir_Op<string mnemonic, list<Trait> traits = []>
    : Op<Oir_Dialect, mnemonic, traits>;

#endif // ZKC_DIALECT_OIR_DIALECT_TD
