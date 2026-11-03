module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.ChaumPedersenProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:9aa55a5711d68922a1d719fb0d37d51dc2428db1bf559de18724ced7d5ce8f7d"
  candidate := "sha256:01a8b6ae803df270a8a3781319753290bde712e6a47d4f66e4e8a5729de27913"
  policy := ⟨"zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [6], [0, 1, 2, 3], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_66697273745f636f6d6d69746d656e74_0" "label_66697273745f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", [], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [4, 5, 6], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_7365636f6e645f636f6d6d69746d656e74_0" "label_7365636f6e645f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", [], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [7, 8, 9], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", [], ["query", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [10, 11], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", [], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [13, 12, 14], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_726573706f6e7365_0" "label_726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", [], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩, [15, 16, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 16], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [1, 12], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [5, 20], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [19, 21], [.data .boolean], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 16], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [3, 12], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [8, 24], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [23, 25], [.data .boolean], []⟩,
    ⟨.calculate .booleanAnd, [22, 26], [.data .boolean], []⟩]
  returned := [27, 18]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.ChaumPedersenProofParticipant
