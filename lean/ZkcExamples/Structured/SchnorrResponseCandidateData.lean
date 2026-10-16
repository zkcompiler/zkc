module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SchnorrResponseCandidateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:1abe45ff8632983228b8c0a74383f42eab5a6461f6adf5a479e0aa6d8c0e407d"
  entry := "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s16h7363686e6f72725f726573706f6e73658h526573706f6e7365", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]

end ZkcExamples.Structured.SchnorrResponseCandidateData
