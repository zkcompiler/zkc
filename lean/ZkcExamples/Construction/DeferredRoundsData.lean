module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Construction.DeferredRoundsData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:82600bde6a020cade986703063b92038eea6bc63938ce0a54793ffac327ee7e6"
  entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"example::Rounds", [("F", (.field "bls12-381.fr"))]⟩), (.block [.instruction (.exchange "role00000000" "role00000001") [1] [.field "bls12-381.fr"] [] "label_6d30_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.draw "role00000001" "bls12-381.fr") [4] [.field "bls12-381.fr"] [] "label_6330", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "label_6430_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [3, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [7, 1] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.field "bls12-381.fr"] [] "label_6d31_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.draw "role00000001" "bls12-381.fr") [11] [.field "bls12-381.fr"] [] "label_6331", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "label_6431_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [6, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [0, 13] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [5, 4] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [0, 15] [.field "bls12-381.fr"] [] "", .instruction (.fieldEqual "bls12-381.fr") [2, 0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }

end ZkcExamples.Construction.DeferredRoundsData
