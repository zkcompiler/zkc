module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SchnorrHelpersData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:e467e83cb2fd4c3736451008e8ae9af3526752618ab8216c597bfed0cc892e82"
  entry := "s13h7363686e6f72725f666f726d7315h48656c7065727350726f746f636f6c"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s13h7363686e6f72725f666f726d7315h48656c7065727350726f746f636f6c", .protocol, .publicDef, [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], [["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000000" "bls12-381.fr") [3] [.field "bls12-381.fr"] [] "s0", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [1, 0] [.group "bls12-381.g1"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.group "bls12-381.g1"] [] "label_636f6d6d69746d656e74_0", .instruction (.restrict ["role00000001"]) [0] [.group "bls12-381.g1"] [] "", .instruction (.draw "role00000001" "bls12-381.fr") [8] [.field "bls12-381.fr"] [] "label_6368616c6c656e6765", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.call "s13h7363686e6f72725f666f726d738h726573706f6e7365") [6, 0, 9] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.field "bls12-381.fr"] [] "label_726573706f6e7365_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.call "s13h7363686e6f72725f666f726d738h6571756174696f6e") [10, 11, 6, 5, 0] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"s13h7363686e6f72725f666f726d738h726573706f6e7365", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], none, [], none, (.block [.instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩, .function ⟨"s13h7363686e6f72725f666f726d738h6571756174696f6e", .math, .privateDef, [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], none, [], none, (.block [.instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [0, 4] [.group "bls12-381.g1"] [] "", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [2, 4] [.group "bls12-381.g1"] [] "", .instruction (.groupAdd "bls12-381.g1") [4, 0] [.group "bls12-381.g1"] [] "", .instruction (.groupEqual "bls12-381.g1") [2, 0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s13h7363686e6f72725f666f726d7315h48656c7065727350726f746f636f6c", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }

end ZkcExamples.Structured.SchnorrHelpersData
