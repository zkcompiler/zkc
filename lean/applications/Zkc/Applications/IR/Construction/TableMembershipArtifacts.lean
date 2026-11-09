module

public import Zkc.IR.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.TableMembershipArtifacts.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:e3e3cdff8c3859466ff580e84184d18757038ca283fe0f09f5b3891d2108f6c5"
  candidate := "sha256:29c9aa7444a5be351fe9a8a63ae80ab26780dabbee57d992242b07ff8db8a41d"
  policy := ⟨"zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e", "role00000000", "role00000001", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := []
  outputs := []
  instructions := [
]
  returned := []

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [], services := [] }

end ZkcExamples.Construction.TableMembershipArtifacts.Producer

namespace ZkcExamples.Construction.TableMembershipArtifacts.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:e3e3cdff8c3859466ff580e84184d18757038ca283fe0f09f5b3891d2108f6c5"
  candidate := "sha256:29c9aa7444a5be351fe9a8a63ae80ab26780dabbee57d992242b07ff8db8a41d"
  policy := ⟨"zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e", "role00000000", "role00000001", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "koala-bear"), .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a517565727936343a62313532646330316339343439373739363761393363373230626630663239383639343062396538626136376637303566653030356162336465653066303566313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.boolean) (.cons (.field "koala-bear") (.nil)))))]
  outputs := [.data .boolean]
  instructions := [
    ⟨.call "zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470", [0, 1], [.data .boolean], []⟩]
  returned := [2]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }

end ZkcExamples.Construction.TableMembershipArtifacts.Validator

namespace ZkcExamples.Construction.TableMembershipArtifacts

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.TableMembershipArtifacts
