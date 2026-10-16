module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SumcheckClaimCandidateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:6295c04cb49a56a3bc438d6979c8e05bc18461d8a2111a3bb57fdd9efbe3b935"
  entry := "s14h73756d636865636b5f636c61696d5h436c61696d"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s14h73756d636865636b5f636c61696d5h436c61696d", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], none, (.block [.instruction (.fieldConstant "bls12-381.fr" "1") [] [.field "bls12-381.fr"] [] "", .instruction (.fieldSubtract "bls12-381.fr") [0, 3] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [0, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [5, 4] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d5h636c61696d", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldConstant "bls12-381.fr" "1") [] [.field "bls12-381.fr"] [] "", .instruction (.fieldSubtract "bls12-381.fr") [0, 3] [.field "bls12-381.fr"] [] "", .instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [2, 0] [.field "bls12-381.fr"] [] "", .instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [4, 5] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d8h7765696768746564", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s14h73756d636865636b5f636c61696d5h436c61696d", []⟩]

end ZkcExamples.Structured.SumcheckClaimCandidateData
