module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.ComposedSumcheckProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:c6412e9dbfd654c98cabfb516f7e747b44b370e14d618d122c483b0f60ee20d3"
  candidate := "sha256:5fc944428aa724030441283efc76355b9a252e1813e06c1eae06db77b9101ab4"
  policy := ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [5], [0, 1, 2, 3, 4], [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.call "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", [2], [.data (.resourceUnit "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.call "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", [6, 7, 8], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.loop "apply_14_label_6c656674_s18" 4, [4, 9, 10, 5], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [⟨[.data .index, .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.receive "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [16, 11], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_6c656674", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [14, 15, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.receive "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [20, 11], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_6c656674", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [18, 19, 21], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [15, 19], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [13, 23], [.data .boolean], []⟩,
        ⟨.guard "apply_14_label_6c656674_s27", [24], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [25, 11], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_6c656674", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [22, 26], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [29, 11], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_6c656674", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [28, 27, 30], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [12, 27], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldConstant "bls12-381.fr" 1), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldSubtract "bls12-381.fr"), [33, 27], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [34, 15], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [27, 19], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [35, 36], [.data (.field "bls12-381.fr")], []⟩], [32, 37, 31]⟩]⟩,
    ⟨.call "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", [11, 12], [.data (.resourceUnit "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.call "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [0, 14, 15, 16], [.data .boolean], []⟩,
    ⟨.call "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", [3], [.data (.resourceUnit "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.call "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", [18, 19, 20], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.loop "apply_16_label_7269676874_s18" 4, [4, 21, 22, 13], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [⟨[.data .index, .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.receive "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [28, 23], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_7269676874", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [26, 27, 29], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.receive "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [32, 23], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_7269676874", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [30, 31, 33], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [27, 31], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [25, 35], [.data .boolean], []⟩,
        ⟨.guard "apply_16_label_7269676874_s27", [36], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [37, 23], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_7269676874", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["query", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [34, 38], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [41, 23], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", [.apply "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" "label_7269676874", .repeat "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d" "s18"], ["message", "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [40, 39, 42], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [24, 39], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldConstant "bls12-381.fr" 1), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldSubtract "bls12-381.fr"), [45, 39], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [46, 27], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [39, 31], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [47, 48], [.data (.field "bls12-381.fr")], []⟩], [44, 49, 43]⟩]⟩,
    ⟨.call "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", [23, 24], [.data (.resourceUnit "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.call "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [1, 26, 27, 28], [.data .boolean], []⟩,
    ⟨.mathBranch, [17, 29], [.data .boolean], [⟨[.data .boolean], [], [0]⟩, ⟨[.data .boolean], [
        ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩], [1]⟩]⟩]
  returned := [30, 25]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.ComposedSumcheckProofParticipant
