module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.OkamotoProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:fc72dc1496212a6408907454c41a32771a9cc502bf1a0cfd96f42e7c255a33e1"
  candidate := "sha256:e5dd4c44b0afb781582895852f8410c851dc37daaccc3fb5d7822e33ac56ccd2"
  policy := ⟨"zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [6], [0, 1, 2], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", [], ["message", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [3, 4, 5], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", [], ["query", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [6, 7], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", [], ["message", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [9, 8, 10], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_66697273745f726573706f6e7365_0" "label_66697273745f726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", [], ["message", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", "label_66697273745f726573706f6e7365_0", "label_66697273745f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [11, 12, 13], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "label_7365636f6e645f726573706f6e7365_0" "label_7365636f6e645f726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", [], ["message", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", "label_7365636f6e645f726573706f6e7365_0", "label_7365636f6e645f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [14, 15, 16], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 12], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [1, 15], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [18, 19], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 8], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [4, 21], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [20, 22], [.data .boolean], []⟩]
  returned := [23, 17]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.OkamotoProofParticipant
