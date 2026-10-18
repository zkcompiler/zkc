module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.TotalStateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:cd8f60eddde3e8137e8b9fad05bcd16236660178098df1be0f34641a021d8a4a"
  entry := "main"
  domains := [⟨"items", [.vector "bls12-381.fr"], .indices 0 0⟩]
  relations := []
  bindings := []
  definitions := [.function ⟨"step", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .index, .vector "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], none, [⟨2, 3, 0⟩], none, (.block [.instruction (.boundedAt "bls12-381.fr") [3, 2] [.field "bls12-381.fr"] [] ""] (.ret [2, 0]))⟩, .function ⟨"main", .protocol, .publicDef, [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["P"], [["P"], ["P"], ["P"]], [["P"], ["P"]]⟩, [], none, (.block [.instruction (.fold "items" "step" "") [0, 1, 2] [.field "bls12-381.fr", .field "bls12-381.fr"] [] ""] (.ret [0, 1]))⟩]
  contracts := [⟨"main", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }

end ZkcExamples.Structured.TotalStateData
