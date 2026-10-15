module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.TotalStateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:cd8f60eddde3e8137e8b9fad05bcd16236660178098df1be0f34641a021d8a4a"
  entry := "main"
  role := "P"
  domains := [⟨"items", [.vector "bls12-381.fr"], .indices 0 0⟩]
  definitions := [.function ⟨"step", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .index, .vector "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], [⟨2, 3, 0⟩], none, (.block [.instruction (.boundedAt "bls12-381.fr") [3, 2] [.field "bls12-381.fr"] [] ""] (.ret [2, 0]))⟩, .function ⟨"main", .protocol, .publicDef, [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], [], none, (.block [.instruction (.fold "items" "step" "") [0, 1, 2] [.field "bls12-381.fr", .field "bls12-381.fr"] [] ""] (.ret [0, 1]))⟩]

end ZkcExamples.Structured.TotalStateData
