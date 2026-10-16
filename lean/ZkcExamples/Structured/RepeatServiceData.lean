module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.RepeatServiceData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:ab3ee63e15b546fbdf51a07a8c1676359e064780bf6567d84d3765082f4f7258"
  entry := "s6h73616d706c653h52756e"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.index, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000001" "bls12-381.fr") [1] [.field "bls12-381.fr"] [] "s0", .instruction (.fieldConstant "bls12-381.fr" "0") [] [.field "bls12-381.fr"] [] "", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.protocolRepeat 2 3 ["role00000000", "role00000001"] [["role00000000"], ["role00000001"]]) [3, 0, 2, 4, 5] [.field "bls12-381.fr", .field "bls12-381.fr"] [.region [.index, .field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] (.block [.instruction (.protocolApply "s6h73616d706c654h44726177" ["role00000000", "role00000001"]) [3, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s7", .instruction (.fieldAdd "bls12-381.fr") [3, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [5, 2] [.field "bls12-381.fr"] [] ""] (.yield [1, 0]))] "s6", .instruction (.draw "role00000001" "bls12-381.fr") [6] [.field "bls12-381.fr"] [] "s16", .instruction (.fieldAdd "bls12-381.fr") [2, 0] [.field "bls12-381.fr"] [] ""] (.ret [2, 0]))⟩, .function ⟨"s6h73616d706c654h44726177", .protocol, .publicDef, [.service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000001" "bls12-381.fr") [0] [.field "bls12-381.fr"] [] "s0", .instruction (.draw "role00000001" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s2", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "s5_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [4, 3] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩]
  contracts := [⟨"s6h73616d706c653h52756e", []⟩, ⟨"s6h73616d706c654h44726177", []⟩]

end ZkcExamples.Structured.RepeatServiceData
