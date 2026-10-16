module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SchnorrResponseCandidateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:813bd5c25cdb7fdd486ebd24359a4ef81c595ae7d74f278f3f4697d0e946d5f7"
  entry := "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s16h7363686e6f72725f726573706f6e73658h526573706f6e7365", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s16h7363686e6f72725f726573706f6e73658h526573706f6e7365", []⟩]

end ZkcExamples.Structured.SchnorrResponseCandidateData
