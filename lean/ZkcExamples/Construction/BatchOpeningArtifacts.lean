module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.BatchOpeningArtifacts.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:d8986d50b476e7fd83721e424071045a6d0ae7ed3eaacf54f2e8d39bb5370422"
  candidate := "sha256:5b857b8ff099c9e6828db824b952ceb39d5e8d74c89fe357322337e3bb9d6cf3"
  policy := ⟨"zkl_206d594942dc6f123848ad35c8fcdc7017b483db9ccd5c0651d1ad5c850eceab", "role00000000", "role00000001", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))]
  outputs := []
  instructions := [
    ⟨.send "label_6261746368_0" "label_6261746368_0" "role00000001", [0], [], []⟩]
  returned := []

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }

end ZkcExamples.Construction.BatchOpeningArtifacts.Producer

namespace ZkcExamples.Construction.BatchOpeningArtifacts.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:d8986d50b476e7fd83721e424071045a6d0ae7ed3eaacf54f2e8d39bb5370422"
  candidate := "sha256:5b857b8ff099c9e6828db824b952ceb39d5e8d74c89fe357322337e3bb9d6cf3"
  policy := ⟨"zkl_206d594942dc6f123848ad35c8fcdc7017b483db9ccd5c0651d1ad5c850eceab", "role00000000", "role00000001", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear")]
  outputs := [.data .boolean, .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))]
  instructions := [
    ⟨.receive "label_6261746368_0" "label_6261746368_0" "role00000000" (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), [], [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))], []⟩,
    ⟨.call "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", [0, 1, 2], [.data .boolean], []⟩]
  returned := [3, 2]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }

end ZkcExamples.Construction.BatchOpeningArtifacts.Validator

namespace ZkcExamples.Construction.BatchOpeningArtifacts

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.BatchOpeningArtifacts
