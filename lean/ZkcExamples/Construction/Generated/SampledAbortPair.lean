module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.SampledAbortPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:05855e7869890c3ee385d1b9e161253355a6cbc2faf534b2fdd5b5eec24c4ddd"
  candidate := "sha256:196f15e5dfa10ae55a2ac5ab2af3d2e8d24f3cac2185a88236d1d8e0e2dac08b"
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

end ZkcExamples.Construction.Generated.SampledAbortPair.Producer

namespace ZkcExamples.Construction.Generated.SampledAbortPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:05855e7869890c3ee385d1b9e161253355a6cbc2faf534b2fdd5b5eec24c4ddd"
  candidate := "sha256:196f15e5dfa10ae55a2ac5ab2af3d2e8d24f3cac2185a88236d1d8e0e2dac08b"
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

end ZkcExamples.Construction.Generated.SampledAbortPair.Validator

namespace ZkcExamples.Construction.Generated.SampledAbortPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.SampledAbortPair
