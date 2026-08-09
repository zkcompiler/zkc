//===- OirTypes.td - Operator-layer types -------------------*- tablegen -*-===//
// Types of the oir dialect (docs/spec/carrier.md §6.1). Values carry
// their birthplace in the type; the sponge state and the proof cursor
// are threaded linear states — pir's token discipline transplanted, so
// absorption order, duplication, and deletion are governed by use-def
// structure.
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_OIR_TYPES_TD
#define ZKC_DIALECT_OIR_TYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Oir/OirDialect.td"

class Oir_Type<string name, string typeMnemonic> : TypeDef<Oir_Dialect, name> {
  let mnemonic = typeMnemonic;
}

def Oir_ValType : Oir_Type<"Val", "val"> {
  let summary = "runtime value with its provenance";
  let description = [{
    `!oir.val<class, origin>` — a verifier-side runtime value. `class`
    mirrors the protocol-layer payload class; `origin` records the
    value's birthplace and is part of the type:

      public   statement argument (caller-asserted)
      pinned   parameter argument (artifact-pinned by digest) or a
               declared constant
      wire     read from the proof stream (adversary-controlled)
      sampled  squeezed from the sponge (uniform)
      derived  computed
      hole     produced by a prover-side compute hole (opaque contract)

    The input channels have distinct integrity disciplines; making
    the discipline a type-level fact is what lets scheme-specific rules
    over adversarial data become type checks. On the prover side the
    same discipline carries the erasure lint: a sampled value is never
    a write operand directly (docs/spec/endpoints.md §2).
  }];
  let parameters = (ins StringRefParameter<"value class">:$valueClass,
                        StringRefParameter<"provenance">:$origin);
  let assemblyFormat = "`<` $valueClass `,` $origin `>`";
  let genVerifyDecl = 1;
}

def Oir_SpongeType : Oir_Type<"Sponge", "sponge"> {
  let summary = "threaded Fiat-Shamir sponge state";
  let description = [{
    `!oir.sponge` — the transcript state. Linear by construction: every
    absorb/squeeze consumes one state and produces the next, so a
    program that reorders, skips, or duplicates an absorption is
    unrepresentable.
  }];
}

def Oir_StreamType : Oir_Type<"Stream", "stream"> {
  let summary = "threaded proof-stream cursor";
  let description = [{
    `!oir.stream` — the proof stream's cursor, threaded like the
    sponge. Whether it is a read cursor (verifier endpoint) or a write
    cursor (prover endpoint) is an endpoint-kind fact, not a type fact.
    On the verifier side `oir.expect_end` consumes the final cursor
    (trailing bytes change V's accept set); on the prover side
    `oir.end_stream` consumes it (the wire is complete).
  }];
}

def Oir_HandleType : Oir_Type<"Handle", "handle"> {
  let summary = "threaded opaque prover-side private state";
  let description = [{
    `!oir.handle<class>` — opaque private state flowing between
    prover-side compute holes: a witness payload, a commitment tree, a
    folded codeword. Threaded linear like sponge and stream: a hole
    that reads a handle consumes the SSA value and re-emits it; the
    final reader consumes without re-emitting, and a handle chain still
    live at `oir.finish` is a defect. Handles never reach the wire,
    never enter the transcript, and never touch pure ops. The class is
    declared by the producing hole contract, or by the artifact's
    witness declaration for block-argument handles.
  }];
  let parameters = (ins StringRefParameter<"handle class">:$handleClass);
  let assemblyFormat = "`<` $handleClass `>`";
}

#endif // ZKC_DIALECT_OIR_TYPES_TD
