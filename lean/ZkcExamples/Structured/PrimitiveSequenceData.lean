module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.PrimitiveSequenceData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:dd4fda31d355f25006f2051123bfc523b1c714138137a4e32cf94d6776d09c52"
  entry := "s18h7072696d69746976655f6578616d706c65738h53657175656e6365"
  domains := []
  relations := []
  bindings := [⟨"zkl_binding_10", "vector.empty", ["bls12-381.fr"], "", some ⟨[.domain "Field" "bls12-381.fr"], [], [.vector "bls12-381.fr"]⟩⟩, ⟨"zkl_binding_9", "field.equal", ["bls12-381.fr"], "", some ⟨[.domain "Field" "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean]⟩⟩, ⟨"zkl_binding_8", "vector.equal", ["bls12-381.fr"], "", some ⟨[.domain "Field" "bls12-381.fr"], [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.boolean]⟩⟩, ⟨"zkl_binding_7", "vector.sum", ["bls12-381.fr"], "", some ⟨[.domain "Field" "bls12-381.fr"], [.vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩⟩, ⟨"zkl_binding_6", "index.sub", [], "", some ⟨[], [.index, .index], [.index]⟩⟩, ⟨"zkl_binding_5", "index.mod", [], "", some ⟨[], [.index, .index], [.index]⟩⟩, ⟨"zkl_binding_4", "index.div", [], "", some ⟨[], [.index, .index], [.index]⟩⟩, ⟨"zkl_binding_3", "vector.append", ["bls12-381.fr"], "", some ⟨[.domain "Field" "bls12-381.fr"], [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩⟩, ⟨"zkl_binding_2", "index.add", [], "", some ⟨[], [.index, .index], [.index]⟩⟩, ⟨"zkl_binding_1", "index.constant", [], "", some ⟨[], [], [.index]⟩⟩, ⟨"zkl_binding_0", "vector.length", ["bls12-381.fr"], "", some ⟨[.domain "Field" "bls12-381.fr"], [.vector "bls12-381.fr"], [.index]⟩⟩]
  definitions := [.function ⟨"s18h7072696d69746976655f6578616d706c65738h53657175656e6365", .protocol, .publicDef, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"], some ⟨["role00000000"], [["role00000000"], ["role00000000"], ["role00000000"]], [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]]⟩, [], some (.protocol ⟨"primitive_examples::Sequence", []⟩), (.block [.instruction (.localCall "s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279" "role00000000") [0, 1, 2] [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"] [] "s0"] (.ret [0, 1, 2, 3, 4, 5, 6, 7]))⟩, .function ⟨"s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", .local, .privateDef, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"], none, [], some (.local "s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279" []), (.block [.instruction (.exec "exec.apply" "zkl_binding_0" []) [0] [.index] [] "s0", .instruction (.exec "exec.apply" "zkl_binding_1" ["1"]) [] [.index] [] "s2", .instruction (.exec "exec.apply" "zkl_binding_2" []) [1, 0] [.index] [] "s3", .instruction (.exec "exec.apply" "zkl_binding_3" []) [3, 4] [.vector "bls12-381.fr"] [] "s5", .instruction (.exec "exec.apply" "zkl_binding_4" []) [1, 6] [.index] [] "s7", .instruction (.exec "exec.apply" "zkl_binding_5" []) [2, 7] [.index] [] "s9", .instruction (.exec "exec.apply" "zkl_binding_1" ["1"]) [] [.index] [] "s11", .instruction (.exec "exec.apply" "zkl_binding_6" []) [4, 0] [.index] [] "s12", .instruction (.exec "exec.apply" "zkl_binding_7" []) [4] [.field "bls12-381.fr"] [] "s14", .instruction (.exec "exec.apply" "zkl_binding_8" []) [9, 5] [.boolean] [] "s16", .instruction (.exec "exec.apply" "zkl_binding_9" []) [1, 11] [.boolean] [] "s18", .instruction (.exec "exec.apply" "zkl_binding_10" []) [] [.vector "bls12-381.fr"] [] "s20"] (.ret [8, 7, 6, 4, 3, 2, 1, 0]))⟩]
  contracts := [⟨"s18h7072696d69746976655f6578616d706c65738h53657175656e6365", []⟩]
  catalogue := { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩], services := [] }
  sourceDeclarations := { records := [], protocols := [] }

end ZkcExamples.Structured.PrimitiveSequenceData
