module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.GuessProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:2a66bcd3e1853a64e66fcf12081dc9ae4591b042bf87968b1e0fd5c499badbf6"
  candidate := "sha256:3639c24732b7fce2def043d3a7b7d4433bc27f6ab4bc8ffb58e401ac717e0180"
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
