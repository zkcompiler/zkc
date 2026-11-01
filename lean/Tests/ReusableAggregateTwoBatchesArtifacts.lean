module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace Tests.ReusableAggregateTwoBatchesArtifacts.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:05e787a9f140ae23ea02292d576482a08471d8017e17e1e88840d246b3118693"
  candidate := "sha256:679fe2ae31c404494567220d567ade415c23efedb58c7fafb1ad867b27ca84dc"
  policy := ⟨"zkl_ccb0c20474f144c8f1737523c09fa681cbd4974bb2edde5304978a97c3573492", "role00000000", "role00000001", 0, "", [], [0, 1, 3, 4], [], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))]
  outputs := []
  instructions := [
    ⟨.send "label_66697273745f6261746368_0" "label_66697273745f6261746368_0" "role00000001", [0], [], []⟩,
    ⟨.send "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "role00000001", [1], [], []⟩]
  returned := []

end Tests.ReusableAggregateTwoBatchesArtifacts.Producer

namespace Tests.ReusableAggregateTwoBatchesArtifacts.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:05e787a9f140ae23ea02292d576482a08471d8017e17e1e88840d246b3118693"
  candidate := "sha256:679fe2ae31c404494567220d567ade415c23efedb58c7fafb1ad867b27ca84dc"
  policy := ⟨"zkl_ccb0c20474f144c8f1737523c09fa681cbd4974bb2edde5304978a97c3573492", "role00000000", "role00000001", 0, "", [], [0, 1, 3, 4], [], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .data (.field "koala-bear"), .data (.field "koala-bear")]
  outputs := [.data .boolean, .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), .data .boolean, .data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))]
  instructions := [
    ⟨.receive "label_66697273745f6261746368_0" "label_66697273745f6261746368_0" "role00000000" (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), [], [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))], []⟩,
    ⟨.call "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", [0, 1, 4], [.data .boolean], []⟩,
    ⟨.receive "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "apply_30_label_7365636f6e645f6261746368_label_6261746368_0" "role00000000" (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil))))), [], [.data (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") (.nil)))))], []⟩,
    ⟨.call "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", [2, 3, 6], [.data .boolean], []⟩]
  returned := [5, 4, 7, 6]

end Tests.ReusableAggregateTwoBatchesArtifacts.Validator

namespace Tests.ReusableAggregateTwoBatchesArtifacts

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end Tests.ReusableAggregateTwoBatchesArtifacts
