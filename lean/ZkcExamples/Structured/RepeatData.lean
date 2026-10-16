module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.RepeatData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:4688782ad99e01fbcaaf32f51b27299e73f4b3a4cf46c7cad1b37b0098667603"
  entry := "zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe", .protocol, .publicDef, [.index, .field "bls12-381.fr", .field "bls12-381.fr", .boolean, .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.protocolRepeat 2 4 ["role00000000", "role00000001"] [["role00000000"], ["role00000001"]]) [0, 1, 2, 3, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [.region [.index, .field "bls12-381.fr", .field "bls12-381.fr", .boolean, .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] (.block [.instruction (.guard "role00000001") [3] [] [] "s4", .instruction (.protocolApply "zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4" ["role00000000", "role00000001"]) [1, 2, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s5"] (.yield [0, 1]))] "s3"] (.ret [0, 1]))⟩, .function ⟨"zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000001" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s0", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "s2_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [3, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [5, 3] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩]

end ZkcExamples.Structured.RepeatData
