module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.TableMembershipArtifacts.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:948ba8a715c8ae5c29f96fa533926344994ad8bf011eb511b5f1fa3977672b12"
  candidate := "sha256:ffc9cc24c0d80f5b2a2fa1058b575111072e9259540ce96cee11c0b8d111d498"
  policy := ⟨"zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e", "role00000000", "role00000001", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := []
  outputs := []
  instructions := [
]
  returned := []

end ZkcExamples.Construction.TableMembershipArtifacts.Producer

namespace ZkcExamples.Construction.TableMembershipArtifacts.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:948ba8a715c8ae5c29f96fa533926344994ad8bf011eb511b5f1fa3977672b12"
  candidate := "sha256:ffc9cc24c0d80f5b2a2fa1058b575111072e9259540ce96cee11c0b8d111d498"
  policy := ⟨"zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e", "role00000000", "role00000001", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "koala-bear"), .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.boolean) (.cons (.field "koala-bear") (.nil)))))]
  outputs := [.data .boolean]
  instructions := [
    ⟨.call "zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470", [0, 1], [.data .boolean], []⟩]
  returned := [2]

end ZkcExamples.Construction.TableMembershipArtifacts.Validator

namespace ZkcExamples.Construction.TableMembershipArtifacts

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.TableMembershipArtifacts
