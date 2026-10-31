module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.RepeatServiceWrapperData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:392198d152fb26744c2093121d09fb6c6fa1ad0843b9c1db65739a8facfae25a"
  entry := "s6h73616d706c655h4f75746572"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s6h73616d706c655h4f75746572", .protocol, .publicDef, [.index, .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001", "role00000002"], [["role00000000", "role00000002"], ["role00000001"], ["role00000000"], ["role00000000"]], [["role00000000"], ["role00000001"], ["role00000002"]]⟩, [], some (.protocol ⟨"sample::Outer", []⟩), (.block [.instruction (.protocolApply "s6h73616d706c653h52756e" ["role00000002", "role00000000"]) [0, 2, 3] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s0"] (.ret [1, 3, 0]))⟩, .function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.index, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Run", []⟩), (.block [.instruction (.draw "role00000001" "bls12-381.fr") [1] [.field "bls12-381.fr"] [] "s0", .instruction (.fieldConstant "bls12-381.fr" "0") [] [.field "bls12-381.fr"] [] "", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.protocolRepeat 2 3 ["role00000000", "role00000001"] [["role00000000"], ["role00000001"]]) [3, 0, 2, 4, 5] [.field "bls12-381.fr", .field "bls12-381.fr"] [.region [.index, .field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] (.block [.instruction (.protocolApply "s6h73616d706c654h44726177" ["role00000000", "role00000001"]) [3, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s7", .instruction (.fieldAdd "bls12-381.fr") [3, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [5, 2] [.field "bls12-381.fr"] [] ""] (.yield [1, 0]))] "s6", .instruction (.draw "role00000001" "bls12-381.fr") [6] [.field "bls12-381.fr"] [] "s16", .instruction (.fieldAdd "bls12-381.fr") [2, 0] [.field "bls12-381.fr"] [] ""] (.ret [2, 0]))⟩, .function ⟨"s6h73616d706c654h44726177", .protocol, .publicDef, [.service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Draw", []⟩), (.block [.instruction (.draw "role00000001" "bls12-381.fr") [0] [.field "bls12-381.fr"] [] "s0", .instruction (.draw "role00000001" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s2", .instruction (.fieldAdd "bls12-381.fr") [1, 0] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "s5_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [4, 3] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩]
  contracts := [⟨"s6h73616d706c655h4f75746572", []⟩, ⟨"s6h73616d706c653h52756e", []⟩, ⟨"s6h73616d706c654h44726177", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.RepeatServiceWrapperData
