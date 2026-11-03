module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:4575d0a452f5749f1fc1c4b338daf73ccc677367c7d65087ae5abf045fb4b6fe"
  candidate := "sha256:cc001b6c8c5d845689ac06e1cd6a44265e43c75d6a3510d5f5128e011dff5a74"
  policy := ⟨"s14h6d697865645f73756d636865636b4h526f6f74", "role00000000", "role00000001", 0, "merlin3.koala-bear.ext8-binomial3.rejection31le/0", [3], [0, 1, 2], [("apply_16_label_726f756e64_label_6368616c6c656e6765", "apply_16_label_726f756e64_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  outputs := [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  instructions := [
    ⟨.call "s14h6d697865645f73756d636865636b5h656d626564", [0], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b5h656d626564", [1], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.send "apply_16_label_726f756e64_label_6c6f77_0" "apply_16_label_726f756e64_label_6c6f77_0" "role00000001", [3], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6c6f77_0", "label_6c6f77_0", "role00000000", "role00000001"]⟩, [2, 3, 5], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.send "apply_16_label_726f756e64_label_68696768_0" "apply_16_label_726f756e64_label_68696768_0" "role00000001", [4], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_68696768_0", "label_68696768_0", "role00000000", "role00000001"]⟩, [6, 4, 7], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.koala-bear.ext8-binomial3.rejection31le/0" "koala-bear.ext8-binomial3" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["query", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6368616c6c656e6765", "input_5", "random.koala-bear.ext8-binomial3/0", "draw", "role00000001"]⟩, [8, 9], [.data (.field "koala-bear.ext8-binomial3"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [11, 10, 12], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩]
  returned := [13]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"merlin3.koala-bear.ext8-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext8-binomial3")], ["FieldTranscript", "IndexTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext8-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Producer

namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:4575d0a452f5749f1fc1c4b338daf73ccc677367c7d65087ae5abf045fb4b6fe"
  candidate := "sha256:cc001b6c8c5d845689ac06e1cd6a44265e43c75d6a3510d5f5128e011dff5a74"
  policy := ⟨"s14h6d697865645f73756d636865636b4h526f6f74", "role00000000", "role00000001", 0, "merlin3.koala-bear.ext8-binomial3.rejection31le/0", [3], [0, 1, 2], [("apply_16_label_726f756e64_label_6368616c6c656e6765", "apply_16_label_726f756e64_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .data (.field "koala-bear"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  instructions := [
    ⟨.call "s14h6d697865645f73756d636865636b5h656d626564", [2], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b7h70656e64696e67", [4], [.data (.resourceUnit "zkl_resource_33f0210ee2b0908c27db5f8d42945742563b41a817cb78a4b3f50a037cfa3396"), .data (.vector "koala-bear.ext8-binomial3"), .data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b10h6f70656e5f636c61696d", [5, 6, 7], [.data (.vector "koala-bear.ext8-binomial3"), .data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.receive "apply_16_label_726f756e64_label_6c6f77_0" "apply_16_label_726f756e64_label_6c6f77_0" "role00000000" (.field "koala-bear.ext8-binomial3"), [], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6c6f77_0", "label_6c6f77_0", "role00000000", "role00000001"]⟩, [3, 10, 11], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.receive "apply_16_label_726f756e64_label_68696768_0" "apply_16_label_726f756e64_label_68696768_0" "role00000000" (.field "koala-bear.ext8-binomial3"), [], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_68696768_0", "label_68696768_0", "role00000000", "role00000001"]⟩, [12, 13, 14], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [10, 13], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldEqual "koala-bear.ext8-binomial3"), [16, 9], [.data .boolean], []⟩,
    ⟨.guard "apply_16_label_726f756e64_s13", [17], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.koala-bear.ext8-binomial3.rejection31le/0" "koala-bear.ext8-binomial3" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["query", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6368616c6c656e6765", "input_5", "random.koala-bear.ext8-binomial3/0", "draw", "role00000001"]⟩, [15, 18], [.data (.field "koala-bear.ext8-binomial3"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [.apply "s14h6d697865645f73756d636865636b4h526f6f74" "label_726f756e64"], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [20, 19, 21], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate (.fieldSubtract "koala-bear.ext8-binomial3"), [13, 10], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldMultiply "koala-bear.ext8-binomial3"), [23, 19], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [10, 24], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", [8, 19], [.data (.vector "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b8h61745f706f696e74", [26, 25], [.data (.resourceUnit "zkl_resource_33f0210ee2b0908c27db5f8d42945742563b41a817cb78a4b3f50a037cfa3396"), .data (.vector "koala-bear.ext8-binomial3"), .data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b5h636865636b", [0, 1, 27, 28, 29], [.data .boolean], []⟩]
  returned := [30, 22]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"merlin3.koala-bear.ext8-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext8-binomial3")], ["FieldTranscript", "IndexTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext8-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Validator

namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair
