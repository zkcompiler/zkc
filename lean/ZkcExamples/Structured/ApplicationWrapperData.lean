module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.ApplicationWrapperData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:1fae8f96381e63971aeda515536a308014969b69d101d80c6dda8c113af03b4a"
  entry := "s6h73616d706c655h4f75746572"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s6h73616d706c655h4f75746572", .protocol, .publicDef, [.boolean, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Outer", []⟩), (.block [.instruction (.protocolApply "s6h73616d706c653h52756e" ["role00000000", "role00000001"]) [0, 1, 2] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s0"] (.ret [0, 1]))⟩, .function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.boolean, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Run", []⟩), (.block [.instruction (.draw "role00000001" "bls12-381.fr") [1] [.field "bls12-381.fr"] [] "s0", .instruction (.guard "role00000001") [1] [] [] "s2", .instruction (.protocolApply "s6h73616d706c654h44726177" ["role00000000", "role00000001"]) [2, 3] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s3", .instruction (.draw "role00000001" "bls12-381.fr") [4] [.field "bls12-381.fr"] [] "s6", .instruction (.fieldAdd "bls12-381.fr") [3, 2] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [0, 1] [.field "bls12-381.fr"] [] ""] (.ret [3, 0]))⟩, .function ⟨"s6h73616d706c654h44726177", .protocol, .publicDef, [.service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Draw", []⟩), (.block [.instruction (.draw "role00000001" "bls12-381.fr") [0] [.field "bls12-381.fr"] [] "s0", .instruction (.draw "role00000001" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s2", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "s5_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [4, 3] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩]
  contracts := [⟨"s6h73616d706c655h4f75746572", []⟩, ⟨"s6h73616d706c653h52756e", []⟩, ⟨"s6h73616d706c654h44726177", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }

end ZkcExamples.Structured.ApplicationWrapperData
