module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.SequentialSigmaPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:6b6b8fdffdb9eb2c66464d0a2f4b0b496e11c955c3ff40cf9dca6834c82472e6"
  candidate := "sha256:6ed8f51241c9c0d5352c1ad1adf620a4e274ca86e9443df358d0340555a0f886"
  policy := ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [6], [0, 1, 2, 3], [("apply_2_s0_label_6368616c6c656e6765", "apply_2_s0_label_64656c6976657279_0"), ("apply_2_s2_label_6368616c6c656e6765", "apply_2_s2_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.localService (⟨"service_5", "role00000000", 5, 5, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["query", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "s0", "input_3", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 6], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "apply_2_s0_label_636f6d6d69746d656e74_0" "apply_2_s0_label_636f6d6d69746d656e74_0" "role00000001", [7], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [5, 7, 8], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["query", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_6368616c6c656e6765", "input_4", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [9, 10], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [12, 11, 13], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [11, 4], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [6, 15], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.send "apply_2_s0_label_726573706f6e7365_0" "apply_2_s0_label_726573706f6e7365_0" "role00000001", [16], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩, [14, 16, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.localService (⟨"service_5", "role00000000", 5, 5, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["query", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "s0", "input_5", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 19], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "role00000001", [20], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [18, 20, 21], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 19], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "role00000001", [23], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [22, 23, 24], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["query", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [25, 26], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [28, 27, 29], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [27, 4], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [19, 31], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.send "apply_2_s2_label_726573706f6e7365_0" "apply_2_s2_label_726573706f6e7365_0" "role00000001", [32], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩, [30, 32, 33], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]
  returned := [34]
  servicePorts := [⟨"service_5", "role00000000", 5, 5, "random.bls12-381.fr/0"⟩]

end ZkcExamples.Construction.Generated.SequentialSigmaPair.Producer

namespace ZkcExamples.Construction.Generated.SequentialSigmaPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:6b6b8fdffdb9eb2c66464d0a2f4b0b496e11c955c3ff40cf9dca6834c82472e6"
  candidate := "sha256:6ed8f51241c9c0d5352c1ad1adf620a4e274ca86e9443df358d0340555a0f886"
  policy := ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [6], [0, 1, 2, 3], [("apply_2_s0_label_6368616c6c656e6765", "apply_2_s0_label_64656c6976657279_0"), ("apply_2_s2_label_6368616c6c656e6765", "apply_2_s2_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "apply_2_s0_label_636f6d6d69746d656e74_0" "apply_2_s0_label_636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_636f6d6d69746d656e74_0", "label_636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [4, 5, 6], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["query", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_6368616c6c656e6765", "input_4", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [7, 8], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [10, 9, 11], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "apply_2_s0_label_726573706f6e7365_0" "apply_2_s0_label_726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s0"⟩], ["message", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩, [12, 13, 14], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 13], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [1, 9], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [5, 17], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [16, 18], [.data .boolean], []⟩,
    ⟨.receive "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [15, 20, 21], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [22, 23, 24], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["query", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [25, 26], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [28, 27, 29], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "apply_2_s2_label_726573706f6e7365_0" "apply_2_s2_label_726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6515h53657175656e7469616c5369676d61", [⟨"apply", "s7h6578616d706c6515h53657175656e7469616c5369676d61", "s2"⟩], ["message", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", "label_726573706f6e7365_0", "label_726573706f6e7365_0", "role00000000", "role00000001"]⟩, [30, 31, 32], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 31], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [1, 27], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [20, 35], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [34, 36], [.data .boolean], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 31], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [3, 27], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupAdd "bls12-381.g1"), [23, 39], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.calculate (.groupEqual "bls12-381.g1"), [38, 40], [.data .boolean], []⟩,
    ⟨.calculate .booleanAnd, [37, 41], [.data .boolean], []⟩,
    ⟨.calculate .booleanAnd, [19, 42], [.data .boolean], []⟩]
  returned := [43, 33]

end ZkcExamples.Construction.Generated.SequentialSigmaPair.Validator

namespace ZkcExamples.Construction.Generated.SequentialSigmaPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.SequentialSigmaPair
