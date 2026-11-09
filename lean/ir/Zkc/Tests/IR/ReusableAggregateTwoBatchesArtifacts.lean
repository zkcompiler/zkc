module

public import Zkc.IR.Construction.AuthoredPair

@[expose] public section

namespace Tests.ReusableAggregateTwoBatchesArtifacts.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:ad36b895eebbef2fc68c991ac686bf0d478e9c421c9d2c55be960c78d2452434"
  candidate := "sha256:a6f9c803df6df2c3433088a26acc1efc48f3ffcb95ba600c3ccf3db87fca3ebe"
  policy := ⟨"zkl_ccb0c20474f144c8f1737523c09fa681cbd4974bb2edde5304978a97c3573492", "role00000000", "role00000001", 0, "", [], [0, 1, 3, 4], [], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))]
  outputs := []
  instructions := [
    ⟨.send "label_66697273745f6261746368_0" "label_66697273745f6261746368_0" "role00000001", [0], [], []⟩,
    ⟨.send "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "role00000001", [1], [], []⟩]
  returned := []

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }

end Tests.ReusableAggregateTwoBatchesArtifacts.Producer

namespace Tests.ReusableAggregateTwoBatchesArtifacts.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:ad36b895eebbef2fc68c991ac686bf0d478e9c421c9d2c55be960c78d2452434"
  candidate := "sha256:a6f9c803df6df2c3433088a26acc1efc48f3ffcb95ba600c3ccf3db87fca3ebe"
  policy := ⟨"zkl_ccb0c20474f144c8f1737523c09fa681cbd4974bb2edde5304978a97c3573492", "role00000000", "role00000001", 0, "", [], [0, 1, 3, 4], [], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .data (.field "koala-bear"), .data (.field "koala-bear")]
  outputs := [.data .boolean, .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), .data .boolean, .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))]
  instructions := [
    ⟨.receive "label_66697273745f6261746368_0" "label_66697273745f6261746368_0" "role00000000" (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), [], [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))], []⟩,
    ⟨.call "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", [0, 1, 4], [.data .boolean], []⟩,
    ⟨.receive "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "role00000000" (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), [], [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e6736343a31303462613033366637316166353564636336373163613231373437396161643861393166646635333937663339666438623839623731373165623638623031313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))], []⟩,
    ⟨.call "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", [2, 3, 6], [.data .boolean], []⟩]
  returned := [5, 4, 7, 6]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }

end Tests.ReusableAggregateTwoBatchesArtifacts.Validator

namespace Tests.ReusableAggregateTwoBatchesArtifacts

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end Tests.ReusableAggregateTwoBatchesArtifacts
