module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.PolynomialRestrictionData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:a764f0cab8ab2963124c37e3a1151bd26b784d0e3cc4e7e610bf8a7ed51d8f20"
  entry := "s22h706f6c796e6f6d69616c5f7265737472696374696f6e11h5265737472696374696f6e"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s22h706f6c796e6f6d69616c5f7265737472696374696f6e11h5265737472696374696f6e", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]]⟩, [], none, (.block [.instruction (.call "zkl_cc6a01baa45918f376cb6ffba1012908fa5bb9dc3dea3db7ae9aa4c1234e154e") [0, 1, 2, 3, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "", .instruction (.call "zkl_46b4d88e04a6cc2620fbb8d192b97f457501737e0adf33682df330fcdd974078") [0, 1, 7] [.field "bls12-381.fr"] [] ""] (.ret [1, 2, 0, 9]))⟩, .function ⟨"zkl_cc6a01baa45918f376cb6ffba1012908fa5bb9dc3dea3db7ae9aa4c1234e154e", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 4] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [5, 6] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [5, 0] [.field "bls12-381.fr"] [] ""] (.ret [2, 0]))⟩, .function ⟨"zkl_46b4d88e04a6cc2620fbb8d192b97f457501737e0adf33682df330fcdd974078", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s22h706f6c796e6f6d69616c5f7265737472696374696f6e11h5265737472696374696f6e", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }

end ZkcExamples.Structured.PolynomialRestrictionData
