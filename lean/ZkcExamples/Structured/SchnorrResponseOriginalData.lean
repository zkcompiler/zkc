module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SchnorrResponseOriginalData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:c96b26425687957a40f1685a38174a01d933d8237c335e3575b5c9ff1b19d5cc"
  entry := "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s16h7363686e6f72725f726573706f6e73658h526573706f6e7365", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.call "s16h7363686e6f72725f726573706f6e73658h726573706f6e7365") [0, 1, 2] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]

end ZkcExamples.Structured.SchnorrResponseOriginalData
