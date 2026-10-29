module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.Generated.Bindings.SampledAbortData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:6737cab668c409b88da52bee9373e0a6e6009832ba1f4210657e7c4b27c790cd"
  entry := "s7h6578616d706c6512h53616d706c656441626f7274"
  domains := []
  relations := [⟨"s7h6578616d706c655h457175616c", .publicDef, "zkc.language.formula/0", "s7h6578616d706c655h457175616c", "9c835c1a401867f6466147d6445185c5567b3aebe60ba75d1646dbdee200f4cc", [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], ["statement", "witness"], some ("zkf_fe5e2a3c5bbade8b5ce48ffd090142e127cc04ea947d1766a7f847161f657190"), []⟩]
  bindings := []
  definitions := [.function ⟨"s7h6578616d706c6512h53616d706c656441626f7274", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"example::SampledAbort", []⟩), (.block [.instruction (.statement "s7h6578616d706c655h457175616c" ["role00000001", "role00000000"] 0 (some ("equality"))) [0, 1] [] [] "", .instruction (.draw "role00000000" "bls12-381.fr") [2] [.field "bls12-381.fr"] [] "s0", .instruction (.fieldConstant "bls12-381.fr" "0") [] [.field "bls12-381.fr"] [] "", .instruction (.fieldEqual "bls12-381.fr") [1, 0] [.boolean] [] "", .instruction (.booleanConstant false) [] [.boolean] [] "", .instruction (.booleanEqual) [1, 0] [.boolean] [] "", .instruction (.guard "role00000000") [0] [] [] "s6", .instruction (.exchange "role00000000" "role00000001") [5] [.field "bls12-381.fr"] [] "label_636f6d6d69746d656e74_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.draw "role00000001" "bls12-381.fr") [10] [.field "bls12-381.fr"] [] "label_6368616c6c656e6765", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"zkf_fe5e2a3c5bbade8b5ce48ffd090142e127cc04ea947d1766a7f847161f657190", .math, .privateDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], none, [], none, (.block [.instruction (.fieldEqual "bls12-381.fr") [0, 1] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s7h6578616d706c6512h53616d706c656441626f7274", [⟨.target, "equality", ⟨"s7h6578616d706c655h457175616c", [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000000"⟩]⟩, none, some (⟨.output, 0, "role00000001"⟩)⟩]⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.Generated.Bindings.SampledAbortData
