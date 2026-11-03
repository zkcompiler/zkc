module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.SchnorrProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:e0e6520563aadb939aaac48414f14606e424c87e3c4f63d287e31479eb6f4d13"
  candidate := "sha256:541268dea4cc1b1af6210452e2da74d30a261e09fa9cc7df43b96ec372d36e6e"
  policy := ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [4], [0, 1], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [2, 3, 4], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["query", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_6368616c6c656e6765", "input_4", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [5, 6], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [8, 7, 9], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_726573706f6e7365_0" "label_726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", [], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩, [10, 11, 12], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 11], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [1, 7], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [3, 15], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [14, 16], [.data .boolean], []⟩]
  returned := [17, 13]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.SchnorrProofParticipant
