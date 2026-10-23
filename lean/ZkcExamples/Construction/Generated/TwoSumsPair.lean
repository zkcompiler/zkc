module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.TwoSumsPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:3b69a20a3bf1c12e4fcfe7cb521bde2f3bb57b6de6fa094caa966248e366553e"
  candidate := "sha256:5dd732f36008ef6ee75ba430df404fd66d91abaf4de509052cef05cd05a5865c"
  policy := ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [5], [0, 1, 2, 3, 4], [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", [0, 2, 4], [.data (.vector "bls12-381.fr"), .data .index, .data .index], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.calculate .indexEqual, [7, 8], [.data .boolean], []⟩,
    ⟨.guard "apply_14_label_6c656674_s3", [9], [], []⟩,
    ⟨.call "s3h7a6b637h696e64696365734h6c657373", [6, 2], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [10, 11], [.data .boolean], []⟩,
    ⟨.guard "apply_14_label_6c656674_s8", [12], [], []⟩,
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "apply_14_label_6c656674_s15" 4 [35, 36, 37, 38, 34], [2, 5, 6, 7, 13, 3], [.data (.vector "bls12-381.fr"), .data .index, .data .index, .data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.call "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", [15, 16, 17], [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.send "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000001", [20], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [22, 14], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [19, 20, 23], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.send "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000001", [21], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [25, 14], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [24, 21, 26], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [28, 14], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [27, 29], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [32, 14], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [31, 30, 33], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", [15, 16, 17, 30], [.data (.vector "bls12-381.fr"), .data .index, .data .index], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [18, 30], [.data (.vector "bls12-381.fr")], []⟩]⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", [1, 2, 19], [.data (.vector "bls12-381.fr"), .data .index, .data .index], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.calculate .indexEqual, [22, 23], [.data .boolean], []⟩,
    ⟨.guard "apply_16_label_7269676874_s3", [24], [], []⟩,
    ⟨.call "s3h7a6b637h696e64696365734h6c657373", [21, 2], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [25, 26], [.data .boolean], []⟩,
    ⟨.guard "apply_16_label_7269676874_s8", [27], [], []⟩,
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "apply_16_label_7269676874_s15" 4 [50, 51, 52, 53, 49], [2, 20, 21, 22, 28, 18], [.data (.vector "bls12-381.fr"), .data .index, .data .index, .data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.call "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", [30, 31, 32], [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.send "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000001", [35], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [37, 29], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [34, 35, 38], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.send "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000001", [36], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [40, 29], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [39, 36, 41], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [43, 29], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [42, 44], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [47, 29], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [46, 45, 48], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", [30, 31, 32, 45], [.data (.vector "bls12-381.fr"), .data .index, .data .index], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [33, 45], [.data (.vector "bls12-381.fr")], []⟩]⟩]
  returned := [33]

end ZkcExamples.Construction.Generated.TwoSumsPair.Producer

namespace ZkcExamples.Construction.Generated.TwoSumsPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:3b69a20a3bf1c12e4fcfe7cb521bde2f3bb57b6de6fa094caa966248e366553e"
  candidate := "sha256:5dd732f36008ef6ee75ba430df404fd66d91abaf4de509052cef05cd05a5865c"
  policy := ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [5], [0, 1, 2, 3, 4], [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "apply_14_label_6c656674_s15" 4 [28, 33, 27], [4, 6, 2, 5], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.receive "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [12, 7], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [10, 11, 13], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.receive "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [16, 7], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [14, 15, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [11, 15], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [9, 19], [.data .boolean], []⟩,
        ⟨.guard "apply_14_label_6c656674_s24", [20], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [21, 7], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [18, 22], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [25, 7], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_6c656674"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [24, 23, 26], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [8, 23], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldConstant "bls12-381.fr" 1), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldSubtract "bls12-381.fr"), [29, 23], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [30, 11], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [23, 15], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [31, 32], [.data (.field "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [0, 7, 8], [.data .boolean], []⟩,
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "apply_16_label_7269676874_s15" 4 [33, 38, 32], [4, 11, 3, 9], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.receive "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [17, 12], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [15, 16, 18], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.receive "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [21, 12], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [19, 20, 22], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [16, 20], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [14, 24], [.data .boolean], []⟩,
        ⟨.guard "apply_16_label_7269676874_s24", [25], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [26, 12], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [23, 27], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [30, 12], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [⟨"apply", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "label_7269676874"⟩, ⟨"repeat", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "s15"⟩], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [29, 28, 31], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [13, 28], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldConstant "bls12-381.fr" 1), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldSubtract "bls12-381.fr"), [34, 28], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [35, 16], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [28, 20], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [36, 37], [.data (.field "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [1, 12, 13], [.data .boolean], []⟩,
    ⟨.calculate .booleanAnd, [10, 15], [.data .boolean], []⟩]
  returned := [16, 14]

end ZkcExamples.Construction.Generated.TwoSumsPair.Validator

namespace ZkcExamples.Construction.Generated.TwoSumsPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.TwoSumsPair
