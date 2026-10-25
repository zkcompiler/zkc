module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.GuessProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:47426e0ec48a7f3e826564a8911d4c7bba1490c409676401cb20557cc2a94c6e"
  candidate := "sha256:b0bc01026e56b9a3062c8df18c6c87be02c0b0145f037178bd7decfbac44a52c"
  policy := ⟨"zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [2], [0], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_6775657373_0" "label_6775657373_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", [], ["message", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", "label_6775657373_0", "label_6775657373_0", "role00000000", "role00000001"]⟩, [1, 2, 3], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", [], ["query", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", "label_6368616c6c656e6765", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [4, 5], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", [], ["message", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [7, 6, 8], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [2, 0], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldEqual "bls12-381.fr"), [10, 6], [.data .boolean], []⟩]
  returned := [11, 9]

end ZkcExamples.Construction.GuessProofParticipant
