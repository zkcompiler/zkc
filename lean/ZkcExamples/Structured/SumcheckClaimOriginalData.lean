module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SumcheckClaimOriginalData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:a5eaa973fd16dc3f0fe8de15944267fa905c5dccae5760ad21e5b42dc90749ef"
  entry := "s14h73756d636865636b5f636c61696d5h436c61696d"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s14h73756d636865636b5f636c61696d5h436c61696d", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], some (.protocol ⟨"sumcheck_claim::Claim", []⟩), (.block [.instruction (.call "s14h73756d636865636b5f636c61696d5h636c61696d") [0, 1, 2] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d5h636c61696d", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldConstant "bls12-381.fr" "1") [] [.field "bls12-381.fr"] [] "", .instruction (.fieldSubtract "bls12-381.fr") [0, 3] [.field "bls12-381.fr"] [] "", .instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [2, 0] [.field "bls12-381.fr"] [] "", .instruction (.call "s14h73756d636865636b5f636c61696d8h7765696768746564") [4, 5] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s14h73756d636865636b5f636c61696d8h7765696768746564", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s14h73756d636865636b5f636c61696d5h436c61696d", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }

end ZkcExamples.Structured.SumcheckClaimOriginalData
