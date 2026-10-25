module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.SchnorrAndAliasedPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:b83161f00837afaec7d892931354e12c103ab5e13b6a08a718d8fa263463a0bc"
  candidate := "sha256:6dc15becf0c7ff5fb748a3a5d5a0e5d3dac4af3e4672eb7239171be0c3c7e4a0"
  policy := ⟨"s7h6578616d706c6510h416c6961736564416e64", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3], [("apply_2_s2_label_6368616c6c656e6765", "apply_2_s2_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.localService (⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s0"⟩], ["query", "s7h6578616d706c658h426f72726f776564", "s0", "input_0", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.localService (⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s0"⟩], ["query", "s7h6578616d706c658h426f72726f776564", "s2", "input_1", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.localService (⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "s0", "input_6", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.localService (⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "s2", "input_6", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 9], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "role00000001", [11], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [6, 11, 12], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 10], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "role00000001", [14], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [13, 14, 15], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [16, 17], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [19, 18, 20], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [18, 4], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [9, 22], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.send "apply_2_s2_label_66697273745f726573706f6e7365_0" "apply_2_s2_label_66697273745f726573706f6e7365_0" "role00000001", [23], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f726573706f6e7365_0", "label_66697273745f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [21, 23, 24], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [18, 5], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [10, 26], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.send "apply_2_s2_label_7365636f6e645f726573706f6e7365_0" "apply_2_s2_label_7365636f6e645f726573706f6e7365_0" "role00000001", [27], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f726573706f6e7365_0", "label_7365636f6e645f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [25, 27, 28], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]
  returned := [29]
  servicePorts := [⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩]

end ZkcExamples.Construction.Generated.SchnorrAndAliasedPair.Producer

namespace ZkcExamples.Construction.Generated.SchnorrAndAliasedPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:b83161f00837afaec7d892931354e12c103ab5e13b6a08a718d8fa263463a0bc"
  candidate := "sha256:6dc15becf0c7ff5fb748a3a5d5a0e5d3dac4af3e4672eb7239171be0c3c7e4a0"
  policy := ⟨"s7h6578616d706c6510h416c6961736564416e64", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3], [("apply_2_s2_label_6368616c6c656e6765", "apply_2_s2_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "apply_2_s2_label_66697273745f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [4, 5, 6], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "apply_2_s2_label_7365636f6e645f636f6d6d69746d656e74_0" "role00000000" (.group "bls12-381.g1"), [], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [7, 8, 9], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [10, 11], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [13, 12, 14], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "apply_2_s2_label_66697273745f726573706f6e7365_0" "apply_2_s2_label_66697273745f726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f726573706f6e7365_0", "label_66697273745f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [15, 16, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.receive "apply_2_s2_label_7365636f6e645f726573706f6e7365_0" "apply_2_s2_label_7365636f6e645f726573706f6e7365_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"s7h6578616d706c6510h416c6961736564416e64", [⟨"apply", "s7h6578616d706c6510h416c6961736564416e64", "s2"⟩], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f726573706f6e7365_0", "label_7365636f6e645f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [18, 19, 20], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
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

end ZkcExamples.Construction.Generated.SchnorrAndAliasedPair.Validator

namespace ZkcExamples.Construction.Generated.SchnorrAndAliasedPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.SchnorrAndAliasedPair
