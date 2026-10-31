module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.MapConstantData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:9c1f1050b0c619ad5a6fe423a3b3b99035e12134322a2b7a94bc1d0eb50c7262"
  entry := "s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773"
  domains := [⟨"zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_domain", [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.elements 0, .elements 1, .zip [1, 0]], 0⟩]
  relations := []
  bindings := []
  definitions := [.function ⟨"s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773", .protocol, .publicDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], some (.protocol ⟨"map_examples::ConstantRows", []⟩), (.block [.instruction (.localCall "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773" "role00000000") [0, 1, 2] [.vector "bls12-381.fr"] [] "s0"] (.ret [0]))⟩, .function ⟨"s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", .local, .privateDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], none, [], some (.local "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773" []), (.block [.instruction (.apply "_finite_admission_0") [0, 1, 2] [.vector "bls12-381.fr"] [] "s0"] (.ret [0]))⟩, .function ⟨"zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_body", .local, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], some (.local "zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_body" []), (.block [.instruction (.apply "_mathematical_admission_1") [0, 1, 4] [.field "bls12-381.fr"] [] "body"] (.ret [0]))⟩, .function ⟨"s12h6d61705f6578616d706c65738h636f6e7374616e74", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldConstant "bls12-381.fr" "7") [] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .collect ⟨"_finite_admission_0", .privateDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], "zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_domain", "zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_body", ""⟩, .realization ⟨"_mathematical_admission_1", [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], "s12h6d61705f6578616d706c65738h636f6e7374616e74"⟩]
  contracts := [⟨"s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.MapConstantData
