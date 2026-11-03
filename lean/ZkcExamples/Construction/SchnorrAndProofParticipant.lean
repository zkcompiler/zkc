module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.SchnorrAndProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:bf6d9b48ccaac3830770ced3165477e8e579d638ff19d2a5892997977c2cd89d"
  candidate := "sha256:a74d0d28851415150534887e2021d9a6b1e66b3bc85dc5655a1e582bdf0d4a5b"
  policy := ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_66697273745f636f6d6d69746d656e74_0" "label_66697273745f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [4, 5, 6], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_7365636f6e645f636f6d6d69746d656e74_0" "label_7365636f6e645f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [7, 8, 9], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [10, 11], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [13, 12, 14], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_66697273745f726573706f6e7365_0" "label_66697273745f726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f726573706f6e7365_0", "label_66697273745f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [15, 16, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_7365636f6e645f726573706f6e7365_0" "label_7365636f6e645f726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f726573706f6e7365_0", "label_7365636f6e645f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [18, 19, 20], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 16], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [1, 12], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [5, 23], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [22, 24], [.data .boolean], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 19], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [3, 12], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [8, 27], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [26, 28], [.data .boolean], []⟩,
    ⟨.calculate .booleanAnd, [25, 29], [.data .boolean], []⟩]
  returned := [30, 21]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.SchnorrAndProofParticipant
