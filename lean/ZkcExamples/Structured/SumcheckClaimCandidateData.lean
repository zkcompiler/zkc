module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SumcheckClaimCandidateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:eb67c317349a237c6397559480bf09992fd9c02361ae4ba0bffa54537591354d"
  entry := "s14h73756d636865636b5f636c61696d5h436c61696d"
  role := "role00000000"
  domains := []
  definitions := [.function ⟨"s14h73756d636865636b5f636c61696d5h436c61696d", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [2, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldSubtract "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [4, 3] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d5h636c61696d", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], [], none, (.block [.instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [0, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldSubtract "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [3, 4] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d8h7765696768746564", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]

end ZkcExamples.Structured.SumcheckClaimCandidateData
