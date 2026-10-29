module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace Tests.Generated.GenericOpaqueData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:36f4e928dbf73e1efd57c1f4a4a3b016cd603b9915ad26996f04a436416d02fd"
  entry := "s14h6f70617175655f6578616d706c653h52756e"
  domains := []
  relations := [⟨"zkl_d8fcb957cd2c6eac8b01d1e6c27a29f89fca0dd8ea007e44a2d6fdac60755d7d", .publicDef, "vendor.layer/0", "layer", "0", [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], ["statement", "witness"], none, [(.field "bls12-381.fr"), (.natural "2"), (.natural "7")]⟩, ⟨"zkl_78a2b0a51facf5012220ce40f4c1976820f42e967c0a550623d165a15e1023f8", .publicDef, "vendor.layer/0", "layer", "0", [.field "koala-bear", .field "koala-bear"], [.boolean], ["statement", "witness"], none, [(.field "koala-bear"), (.natural "2"), (.natural "7")]⟩, ⟨"zkl_c2147a7df5515c3ba4e3a465008c1471c8f246b99625baa715f094a4f5b81479", .publicDef, "vendor.layer/0", "layer", "0", [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], ["statement", "witness"], none, [(.field "bls12-381.fr"), (.natural "3"), (.natural "7")]⟩, ⟨"zkl_1225b1d7c5fbb22375d1076026b9e7c004caa03eca8d382d0372111842177a0c", .publicDef, "vendor.layer/0", "layer", "0", [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], ["statement", "witness"], none, [(.field "bls12-381.fr"), (.natural "2"), (.natural "8")]⟩, ⟨"zkl_789c8626cf690d2f6b9b939ef2ca445c885a4bd5fbcb865149637857ec233e65", .publicDef, "vendor.layer/0", "layer", "0", [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean], ["statement", "witness"], none, [(.field "bls12-381.fr"), (.natural "2"), (.natural "7")]⟩]
  bindings := []
  definitions := [.function ⟨"s14h6f70617175655f6578616d706c653h52756e", .protocol, .publicDef, [.field "bls12-381.fr", .field "koala-bear"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"opaque_example::Run", []⟩), (.block [.instruction (.booleanConstant true) [] [.boolean] [] "", .instruction (.restrict ["role00000001"]) [0] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s14h6f70617175655f6578616d706c653h52756e", [⟨.input, "first", ⟨"zkl_d8fcb957cd2c6eac8b01d1e6c27a29f89fca0dd8ea007e44a2d6fdac60755d7d", [⟨.input, 0, "role00000001", false⟩, ⟨.input, 0, "role00000000", false⟩]⟩, none, none⟩, ⟨.input, "other_domain", ⟨"zkl_78a2b0a51facf5012220ce40f4c1976820f42e967c0a550623d165a15e1023f8", [⟨.input, 1, "role00000001", false⟩, ⟨.input, 1, "role00000000", false⟩]⟩, none, none⟩, ⟨.input, "other_natural", ⟨"zkl_c2147a7df5515c3ba4e3a465008c1471c8f246b99625baa715f094a4f5b81479", [⟨.input, 0, "role00000001", false⟩, ⟨.input, 0, "role00000000", false⟩]⟩, none, none⟩, ⟨.input, "other_unused", ⟨"zkl_1225b1d7c5fbb22375d1076026b9e7c004caa03eca8d382d0372111842177a0c", [⟨.input, 0, "role00000001", false⟩, ⟨.input, 0, "role00000000", false⟩]⟩, none, none⟩, ⟨.target, "alias", ⟨"zkl_789c8626cf690d2f6b9b939ef2ca445c885a4bd5fbcb865149637857ec233e65", [⟨.input, 0, "role00000001", false⟩, ⟨.input, 0, "role00000000", false⟩]⟩, none, some (⟨.output, 0, "role00000001", false⟩)⟩]⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end Tests.Generated.GenericOpaqueData
