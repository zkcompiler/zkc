module

public import Zkc.IR.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.SampledAbortPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:cd4c0a3b93ee42896ad8e06e71f899864dbfd130ce984b67a6819e4722f82280"
  candidate := "sha256:ae63aec640685a164644f0021a5f78460e314d679fd806a4920e967bcb1d3949"
  policy := ⟨"s7h6578616d706c6512h53616d706c656441626f7274", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [3], [0], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.localService (⟨"service_2", "role00000000", 2, 2, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["query", "s7h6578616d706c6512h53616d706c656441626f7274", "s0", "input_2", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldConstant "bls12-381.fr" 0), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldEqual "bls12-381.fr"), [3, 4], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [5, 6], [.data .boolean], []⟩,
    ⟨.guard "s6", [7], [], []⟩,
    ⟨.send "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000001", [0], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["message", "s7h6578616d706c6512h53616d706c656441626f7274", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [2, 0, 8], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["query", "s7h6578616d706c6512h53616d706c656441626f7274", "label_6368616c6c656e6765", "input_3", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [9, 10], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["message", "s7h6578616d706c6512h53616d706c656441626f7274", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [12, 11, 13], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]
  returned := [14]
  servicePorts := [⟨"service_2", "role00000000", 2, 2, "random.bls12-381.fr/0"⟩]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [⟨"random.bls12-381.fr/0", "bls12-381.fr", ["draw"]⟩] }

end ZkcExamples.Construction.Generated.SampledAbortPair.Producer

namespace ZkcExamples.Construction.Generated.SampledAbortPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:cd4c0a3b93ee42896ad8e06e71f899864dbfd130ce984b67a6819e4722f82280"
  candidate := "sha256:ae63aec640685a164644f0021a5f78460e314d679fd806a4920e967bcb1d3949"
  policy := ⟨"s7h6578616d706c6512h53616d706c656441626f7274", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [3], [0], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["message", "s7h6578616d706c6512h53616d706c656441626f7274", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [1, 2, 3], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["query", "s7h6578616d706c6512h53616d706c656441626f7274", "label_6368616c6c656e6765", "input_3", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [4, 5], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6512h53616d706c656441626f7274", [], ["message", "s7h6578616d706c6512h53616d706c656441626f7274", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [7, 6, 8], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩]
  returned := [10, 9]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.Generated.SampledAbortPair.Validator

namespace ZkcExamples.Construction.Generated.SampledAbortPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.SampledAbortPair
