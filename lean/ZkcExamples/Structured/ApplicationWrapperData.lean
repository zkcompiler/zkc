module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.ApplicationWrapperData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:3b9b091154fa5a5ff53fb18ae5bd8e13a57c5f2da76b21aa726da537ec8aaae3"
  entry := "s6h73616d706c655h4f75746572"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s6h73616d706c655h4f75746572", .protocol, .publicDef, [.boolean, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.protocolApply "s6h73616d706c653h52756e" ["role00000000", "role00000001"]) [0, 1, 2] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s0"] (.ret [0, 1]))⟩, .function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.boolean, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000001" "bls12-381.fr") [1] [.field "bls12-381.fr"] [] "s0", .instruction (.guard "role00000001") [1] [] [] "s2", .instruction (.protocolApply "s6h73616d706c654h44726177" ["role00000000", "role00000001"]) [2, 3] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s3", .instruction (.draw "role00000001" "bls12-381.fr") [4] [.field "bls12-381.fr"] [] "s6", .instruction (.fieldAdd "bls12-381.fr") [3, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [0, 1] [.field "bls12-381.fr"] [] ""] (.ret [3, 0]))⟩, .function ⟨"s6h73616d706c654h44726177", .protocol, .publicDef, [.service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000001" "bls12-381.fr") [0] [.field "bls12-381.fr"] [] "s0", .instruction (.draw "role00000001" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s2", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "s5_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [4, 3] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩]

end ZkcExamples.Structured.ApplicationWrapperData
