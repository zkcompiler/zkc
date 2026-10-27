module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.PrimitivePureIndexData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:900f92cedcf74bff980087445decb9529bc9bf852af634b4bb9dd2a169a892e3"
  entry := "s18h7072696d69746976655f6578616d706c65739h50757265496e646578"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s18h7072696d69746976655f6578616d706c65739h50757265496e646578", .protocol, .publicDef, [.index], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000"]], [["role00000000"]]⟩, [], some (.protocol ⟨"primitive_examples::PureIndex", []⟩), (.block [.instruction (.indexConstant "0") [] [.index] [] "", .instruction (.indexEqual) [1, 0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s18h7072696d69746976655f6578616d706c65739h50757265496e646578", []⟩]
  catalogue := { nominals := [], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.PrimitivePureIndexData
