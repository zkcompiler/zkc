module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.RepeatData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:9cd5c2b6a90fcfb9cf295c3b43eec130415a8a2454988f12d9f7e530633503c3"
  entry := "zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe", .protocol, .publicDef, [.index, .field "bls12-381.fr", .field "bls12-381.fr", .boolean, .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Run", [("N", (.natural "4"))]⟩), (.block [.instruction (.protocolRepeat 2 4 ["role00000000", "role00000001"] [["role00000000"], ["role00000001"]]) [0, 1, 2, 3, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [.region [.index, .field "bls12-381.fr", .field "bls12-381.fr", .boolean, .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] (.block [.instruction (.guard "role00000001") [3] [] [] "s4", .instruction (.protocolApply "zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4" ["role00000000", "role00000001"]) [1, 2, 4] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s5"] (.yield [0, 1]))] "s3"] (.ret [0, 1]))⟩, .function ⟨"zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000001"], ["role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], some (.protocol ⟨"sample::Round", [("F", (.field "bls12-381.fr"))]⟩), (.block [.instruction (.draw "role00000001" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s0", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "s2_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [3, 0] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [5, 3] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩]
  contracts := [⟨"zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe", []⟩, ⟨"zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.RepeatData
