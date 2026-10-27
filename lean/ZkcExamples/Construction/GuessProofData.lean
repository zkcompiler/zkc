module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Construction.GuessProofData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:47426e0ec48a7f3e826564a8911d4c7bba1490c409676401cb20557cc2a94c6e"
  entry := "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"example::Guess", [("F", (.field "bls12-381.fr"))]⟩), (.block [.instruction (.exchange "role00000000" "role00000001") [1] [.field "bls12-381.fr"] [] "label_6775657373_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.draw "role00000001" "bls12-381.fr") [4] [.field "bls12-381.fr"] [] "label_6368616c6c656e6765", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [3, 5] [.field "bls12-381.fr"] [] "", .instruction (.fieldEqual "bls12-381.fr") [0, 3] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Construction.GuessProofData
