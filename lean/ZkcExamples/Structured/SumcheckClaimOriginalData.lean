module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SumcheckClaimOriginalData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:52bfc392e61817a5c7edd084abb85b779a79d4cbd84508952c1b18f64292e5c2"
  entry := "s14h73756d636865636b5f636c61696d5h436c61696d"
  role := "role00000000"
  domains := []
  definitions := [.function ⟨"s14h73756d636865636b5f636c61696d5h436c61696d", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], [], none, (.block [.instruction (.call "s14h73756d636865636b5f636c61696d5h636c61696d") [0, 1, 2] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d5h636c61696d", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], [], none, (.block [.instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [0, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldSubtract "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [3, 4] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d8h7765696768746564", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]

end ZkcExamples.Structured.SumcheckClaimOriginalData
