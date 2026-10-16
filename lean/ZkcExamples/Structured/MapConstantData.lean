module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.MapConstantData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:8bab500d829212e56a82e43e514c9f300d875b15d87a1e7923fe7cb62f235195"
  entry := "s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773"
  domains := []
  relations := []
  bindings := []
  definitions := [.map ⟨"zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96", [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], "s12h6d61705f6578616d706c65738h636f6e7374616e74", [true, true, false]⟩, .function ⟨"s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773", .protocol, .publicDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.localCall "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773" "role00000000") [0, 1, 2] [.vector "bls12-381.fr"] [] "s0"] (.ret [0]))⟩, .function ⟨"s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", .local, .publicDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], none, [], some ("s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", []), (.block [.instruction (.apply "zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96") [0, 1, 2] [.vector "bls12-381.fr"] [] "s0"] (.ret [0]))⟩, .function ⟨"s12h6d61705f6578616d706c65738h636f6e7374616e74", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldConstant "bls12-381.fr" "7") [] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]

end ZkcExamples.Structured.MapConstantData
