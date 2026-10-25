module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.MapConstantData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:b34464d24d4efb96f0795c081cb883b883a9e4731936dc5253171d74c86072d6"
  entry := "s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773"
  domains := []
  relations := []
  bindings := []
  definitions := [.map ⟨"zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96", [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], "s12h6d61705f6578616d706c65738h636f6e7374616e74", [true, true, false]⟩, .function ⟨"s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773", .protocol, .publicDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], some (.protocol ⟨"map_examples::ConstantRows", []⟩), (.block [.instruction (.localCall "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773" "role00000000") [0, 1, 2] [.vector "bls12-381.fr"] [] "s0"] (.ret [0]))⟩, .function ⟨"s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", .local, .publicDef, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"], none, [], some (.local "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773" []), (.block [.instruction (.apply "zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96") [0, 1, 2] [.vector "bls12-381.fr"] [] "s0"] (.ret [0]))⟩, .function ⟨"s12h6d61705f6578616d706c65738h636f6e7374616e74", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldConstant "bls12-381.fr" "7") [] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }

end ZkcExamples.Structured.MapConstantData
