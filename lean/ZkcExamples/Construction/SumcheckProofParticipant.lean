module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.SumcheckProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:86cd9b93d888ee210793170516152638bc8f7b8af253f1a052aead232e386437"
  candidate := "sha256:b14e394fa96696a641c820e30b5d4050a3f774b158a3832ea360daf71eab34fa"
  policy := ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [3], [0, 1, 2], [("apply_18_label_726564756365_label_6368616c6c656e6765", "apply_18_label_726564756365_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "apply_18_label_726564756365_s15" 2 [26, 31, 25], [2, 4, 1, 3], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.receive "apply_18_label_726564756365_label_726f756e64_0" "apply_18_label_726564756365_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [10, 5], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [8, 9, 11], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.receive "apply_18_label_726564756365_label_726f756e64_1" "apply_18_label_726564756365_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [14, 5], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [12, 13, 15], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [9, 13], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [7, 17], [.data .boolean], []⟩,
        ⟨.guard "apply_18_label_726564756365_s24", [18], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [19, 5], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [16, 20], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [23, 5], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [22, 21, 24], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [6, 21], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldConstant "bls12-381.fr" 1), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldSubtract "bls12-381.fr"), [27, 21], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [28, 9], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [21, 13], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [29, 30], [.data (.field "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [0, 5, 6], [.data .boolean], []⟩]
  returned := [8, 7]

end ZkcExamples.Construction.SumcheckProofParticipant
