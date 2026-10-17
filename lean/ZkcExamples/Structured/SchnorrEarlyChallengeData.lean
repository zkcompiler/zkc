module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.SchnorrEarlyChallengeData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:ad08c89d953044a25cd88ff4860d184d7f0afd56eb61f0416369167c18e75363"
  entry := "s13h7363686e6f72725f666f726d7322h4561726c794368616c6c656e676550726f746f636f6c"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s13h7363686e6f72725f666f726d7322h4561726c794368616c6c656e676550726f746f636f6c", .protocol, .publicDef, [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], [["role00000001"]]⟩, [], none, (.block [.instruction (.draw "role00000000" "bls12-381.fr") [3] [.field "bls12-381.fr"] [] "s0", .instruction (.draw "role00000001" "bls12-381.fr") [5] [.field "bls12-381.fr"] [] "label_6368616c6c656e6765", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [2, 1] [.group "bls12-381.g1"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.group "bls12-381.g1"] [] "label_636f6d6d69746d656e74_0", .instruction (.restrict ["role00000001"]) [0] [.group "bls12-381.g1"] [] "", .instruction (.exchange "role00000001" "role00000000") [3] [.field "bls12-381.fr"] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [0, 9] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [7, 0] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.field "bls12-381.fr"] [] "label_726573706f6e7365_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [11, 0] [.group "bls12-381.g1"] [] "", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [13, 10] [.group "bls12-381.g1"] [] "", .instruction (.groupAdd "bls12-381.g1") [8, 0] [.group "bls12-381.g1"] [] "", .instruction (.groupEqual "bls12-381.g1") [2, 0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s13h7363686e6f72725f666f726d7322h4561726c794368616c6c656e676550726f746f636f6c", []⟩]

end ZkcExamples.Structured.SchnorrEarlyChallengeData
