module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace Tests.Generated.CompositeReuseData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:ce7aa9626b3f1d89d1c7366ac83f83b1060a30edbc20a4e3c82d17e2592683e9"
  entry := "s9h636f6d706f736974655h5468697264"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s9h636f6d706f736974655h5468697264", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .boolean], [.field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"composite::Third", []⟩), (.block [.instruction (.protocolApply "s9h636f6d706f736974655h4f75746572" ["role00000000", "role00000001"]) [0, 1, 2, 3, 5] [.field "bls12-381.fr"] [] "label_636f6d706f73697465", .instruction (.protocolApply "s9h636f6d706f736974655h5368696674" ["role00000001", "role00000000"]) [1, 0, 5, 6] [.field "bls12-381.fr"] [] "label_6c617374"] (.ret [0]))⟩, .function ⟨"s9h636f6d706f736974655h4f75746572", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .boolean], [.field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"composite::Outer", []⟩), (.block [.instruction (.protocolApply "s9h636f6d706f736974655h5368696674" ["role00000001", "role00000000"]) [0, 1, 2, 4] [.field "bls12-381.fr"] [] "label_6669727374", .instruction (.protocolApply "s9h636f6d706f736974655h5368696674" ["role00000001", "role00000000"]) [1, 0, 4, 5] [.field "bls12-381.fr"] [] "label_7365636f6e64"] (.ret [0]))⟩, .function ⟨"s9h636f6d706f736974655h5368696674", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .boolean], [.field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"]]⟩, [], some (.protocol ⟨"composite::Shift", []⟩), (.block [.instruction (.guard "role00000000") [3] [] [] "s0", .instruction (.fieldAdd "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s9h636f6d706f736974655h5468697264", []⟩, ⟨"s9h636f6d706f736974655h4f75746572", []⟩, ⟨"s9h636f6d706f736974655h5368696674", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end Tests.Generated.CompositeReuseData
