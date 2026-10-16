module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.PrimitivePureIndexData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:3176a2abced8913176e3b4a6baa01f08515f3b7af37b7626d6176f4d72d26ae9"
  entry := "s18h7072696d69746976655f6578616d706c65739h50757265496e646578"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s18h7072696d69746976655f6578616d706c65739h50757265496e646578", .protocol, .publicDef, [.index], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.indexConstant "0") [] [.index] [] "", .instruction (.indexEqual) [1, 0] [.boolean] [] ""] (.ret [0]))⟩]

end ZkcExamples.Structured.PrimitivePureIndexData
