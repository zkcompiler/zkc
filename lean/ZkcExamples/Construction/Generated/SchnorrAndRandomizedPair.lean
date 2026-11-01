module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:3adfa9be4834f650cdf1ae35c6a441d5589c9325627aeb9bec8b8274a6d9e3c0"
  candidate := "sha256:396aa9e964cdcdcbe5c3eb542af8f1eae9d8be9a7580da6cebf96bcd810f689a"
  policy := ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.group "bls12-381.g1"), .data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.localService (⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "s0", "input_6", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.localService (⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩) (Request.draw "bls12-381.fr") ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "s2", "input_6", "random.bls12-381.fr/0", "draw", "role00000000"]⟩ [], [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [0, 7], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "label_66697273745f636f6d6d69746d656e74_0" "label_66697273745f636f6d6d69746d656e74_0" "role00000001", [9], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f636f6d6d69746d656e74_0", "label_66697273745f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [6, 9, 10], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.groupScale "bls12-381.g1" "bls12-381.fr"), [2, 8], [.data (.group "bls12-381.g1")], []⟩,
    ⟨.send "label_7365636f6e645f636f6d6d69746d656e74_0" "label_7365636f6e645f636f6d6d69746d656e74_0" "role00000001", [12], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0", "role00000000", "role00000001"]⟩, [11, 12, 13], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["query", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [14, 15], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [17, 16, 18], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [16, 4], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [7, 20], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.send "label_66697273745f726573706f6e7365_0" "label_66697273745f726573706f6e7365_0" "role00000001", [21], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_66697273745f726573706f6e7365_0", "label_66697273745f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [19, 21, 22], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [16, 5], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [8, 24], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.send "label_7365636f6e645f726573706f6e7365_0" "label_7365636f6e645f726573706f6e7365_0" "role00000001", [25], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", [], ["message", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", "label_7365636f6e645f726573706f6e7365_0", "label_7365636f6e645f726573706f6e7365_0", "role00000000", "role00000001"]⟩, [23, 25, 26], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]
  returned := [27]
  servicePorts := [⟨"service_6", "role00000000", 6, 6, "random.bls12-381.fr/0"⟩]

end ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair.Producer

namespace ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:3adfa9be4834f650cdf1ae35c6a441d5589c9325627aeb9bec8b8274a6d9e3c0"
  candidate := "sha256:396aa9e964cdcdcbe5c3eb542af8f1eae9d8be9a7580da6cebf96bcd810f689a"
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

end ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair.Validator

namespace ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair
