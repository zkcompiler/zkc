module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.RepeatNestedData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:6bdf8003ece0522664ba51c8777fc1c993632ac137ae531e06f733c52d5cdfbc"
  entry := "s6h73616d706c653h52756e"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.index, .index, .field "bls12-381.fr"], [.field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], some (.protocol ⟨"sample::Run", []⟩), (.block [.instruction (.protocolRepeat 1 3 ["role00000000"] [["role00000000"]]) [0, 2, 1, 2] [.field "bls12-381.fr"] [.region [.index, .field "bls12-381.fr", .index, .field "bls12-381.fr"] [.field "bls12-381.fr"] (.block [.instruction (.protocolRepeat 1 2 ["role00000000"] [["role00000000"]]) [2, 1, 3] [.field "bls12-381.fr"] [.region [.index, .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] (.block [.instruction (.fieldAdd "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] ""] (.yield [0]))] "s5"] (.yield [0]))] "s3"] (.ret [0]))⟩]
  contracts := [⟨"s6h73616d706c653h52756e", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.RepeatNestedData
