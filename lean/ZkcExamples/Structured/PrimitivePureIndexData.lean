module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.PrimitivePureIndexData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:07bea68aa2ea72738ca9b8ec214801f68e846d9db1bc68d1b0b0a9f07c5f6429"
  entry := "s18h7072696d69746976655f6578616d706c65739h50757265496e646578"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s18h7072696d69746976655f6578616d706c65739h50757265496e646578", .protocol, .publicDef, [.index], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.indexConstant "0") [] [.index] [] "", .instruction (.indexEqual) [1, 0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s18h7072696d69746976655f6578616d706c65739h50757265496e646578", []⟩]
  catalogue := { nominals := [], services := [] }

end ZkcExamples.Structured.PrimitivePureIndexData
