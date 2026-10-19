module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.ComposedSumcheckProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:228377c90fcb62e9cdadb413a6d846bfb2e6565b4d528345229f005b31f23cda"
  candidate := "sha256:a99d18cb6575d1cd362d9dc2c361f7e82519b4947f4b0ba425c2c570f973c789"
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

end ZkcExamples.Construction.ComposedSumcheckProofParticipant
