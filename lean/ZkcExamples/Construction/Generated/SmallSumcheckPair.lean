module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:86cd9b93d888ee210793170516152638bc8f7b8af253f1a052aead232e386437"
  candidate := "sha256:b14e394fa96696a641c820e30b5d4050a3f774b158a3832ea360daf71eab34fa"
  policy := ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [3], [0, 1, 2], [("apply_18_label_726564756365_label_6368616c6c656e6765", "apply_18_label_726564756365_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.vector "bls12-381.fr"), .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", [0, 1, 3], [.data (.vector "bls12-381.fr"), .data .index, .data .index], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.calculate .indexEqual, [6, 7], [.data .boolean], []⟩,
    ⟨.guard "apply_18_label_726564756365_s3", [8], [], []⟩,
    ⟨.call "s3h7a6b637h696e64696365734h6c657373", [5, 1], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [9, 10], [.data .boolean], []⟩,
    ⟨.guard "apply_18_label_726564756365_s8", [11], [], []⟩,
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "apply_18_label_726564756365_s15" 2 [34, 35, 36, 37, 33], [1, 4, 5, 6, 12, 2], [.data (.vector "bls12-381.fr"), .data .index, .data .index, .data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.call "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", [14, 15, 16], [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.send "apply_18_label_726564756365_label_726f756e64_0" "apply_18_label_726564756365_label_726f756e64_0" "role00000001", [19], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [21, 13], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [18, 19, 22], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.send "apply_18_label_726564756365_label_726f756e64_1" "apply_18_label_726564756365_label_726f756e64_1" "role00000001", [20], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [24, 13], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [23, 20, 25], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [27, 13], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [26, 28], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [31, 13], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [30, 29, 32], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", [14, 15, 16, 29], [.data (.vector "bls12-381.fr"), .data .index, .data .index], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [17, 29], [.data (.vector "bls12-381.fr")], []⟩]⟩]
  returned := [17]

end ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer

namespace ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator
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

end ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator

namespace ZkcExamples.Construction.Generated.SmallSumcheckPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.SmallSumcheckPair
