module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.UnitStateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:23ea8a612a7e08ab69c9ffb5f4b32ed3d4e8b3ea1d485f6d041fa354a19cabfc"
  entry := "main"
  domains := [⟨"items", [.vector "bls12-381.fr"], [.elements 0], 0⟩]
  relations := []
  bindings := []
  definitions := [.function ⟨"step", .local, .privateDef, [.field "bls12-381.fr", .vector "bls12-381.fr", .boolean], [], none, [], some (.local "step" []), (.block [] (.stop .abort "body_stop"))⟩, .function ⟨"predicate", .local, .privateDef, [.field "bls12-381.fr", .vector "bls12-381.fr", .boolean], [.boolean], none, [], some (.local "predicate" []), (.block [] (.ret [2]))⟩, .function ⟨"work", .local, .publicDef, [.vector "bls12-381.fr", .boolean], [.boolean], none, [], some (.local "work" []), (.block [.instruction (.apply "_finite_admission_0") [0, 1] [] [] "fold"] (.ret [1]))⟩, .function ⟨"main", .protocol, .publicDef, [.vector "bls12-381.fr", .boolean], [.boolean], some ⟨["P"], [["P"], ["P"]], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩), (.block [.instruction (.localCall "work" "P") [0, 1] [.boolean] [] "work"] (.ret [0]))⟩, .finite ⟨"_finite_admission_0", .privateDef, [.vector "bls12-381.fr", .boolean], [], "items", "step", "predicate"⟩]
  contracts := [⟨"main", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.UnitStateData
