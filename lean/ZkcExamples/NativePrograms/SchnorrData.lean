module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.NativePrograms.SchnorrData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:9cefb7bb0eff902b7e0c9fbb804ae6d0b3269eee164e2b8019eee1a33ed4fe28"
  entry := "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad"
  domains := []
  relations := [⟨"zkl_dcbf81f97f37c181fef011e003f8b5e033842ddeccb04c1dea551fb7bf94978f", .publicDef, "zkc.language.formula/0", "zkl_dcbf81f97f37c181fef011e003f8b5e033842ddeccb04c1dea551fb7bf94978f", "562e2f862c031123f999b0c041b1ea57c7a97193fe8859de83ce2a0b8932117c", [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr"], [.boolean], ["parameter", "statement", "witness"], some ("zkf_6d5ed5928b9bea74d6d7736ea8056c9f06e280ffdc4dbcaf2e00bf4f639c1873"), []⟩]
  bindings := []
  definitions := [.function ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .protocol, .publicDef, [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"schnorr::Schnorr", [("G", (.group "bls12-381.g1"))]⟩), (.block [.instruction (.draw "role00000000" "bls12-381.fr") [3] [.field "bls12-381.fr"] [] "s0", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [1, 0] [.group "bls12-381.g1"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.group "bls12-381.g1"] [] "label_636f6d6d69746d656e74_0", .instruction (.restrict ["role00000001"]) [0] [.group "bls12-381.g1"] [] "", .instruction (.draw "role00000001" "bls12-381.fr") [8] [.field "bls12-381.fr"] [] "label_6368616c6c656e6765", .instruction (.exchange "role00000001" "role00000000") [0] [.field "bls12-381.fr"] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [0, 9] [.field "bls12-381.fr"] [] "", .instruction (.fieldAdd "bls12-381.fr") [7, 0] [.field "bls12-381.fr"] [] "", .instruction (.exchange "role00000000" "role00000001") [0] [.field "bls12-381.fr"] [] "label_726573706f6e7365_0", .instruction (.restrict ["role00000001"]) [0] [.field "bls12-381.fr"] [] "", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [11, 0] [.group "bls12-381.g1"] [] "", .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [13, 7] [.group "bls12-381.g1"] [] "", .instruction (.groupAdd "bls12-381.g1") [9, 0] [.group "bls12-381.g1"] [] "", .instruction (.groupEqual "bls12-381.g1") [2, 0] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"zkf_6d5ed5928b9bea74d6d7736ea8056c9f06e280ffdc4dbcaf2e00bf4f639c1873", .math, .privateDef, [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr"], [.boolean], none, [], none, (.block [.instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [0, 2] [.group "bls12-381.g1"] [] "", .instruction (.groupEqual "bls12-381.g1") [2, 0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [⟨.target, "knowledge", ⟨"zkl_dcbf81f97f37c181fef011e003f8b5e033842ddeccb04c1dea551fb7bf94978f", [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩, ⟨.input, 2, "role00000000"⟩]⟩, none, some (⟨.output, 0, "role00000001"⟩)⟩]⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.NativePrograms.SchnorrData
