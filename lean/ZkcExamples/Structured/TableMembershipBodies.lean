module

public import Zkc.Protocols.TableMembership.SourceBodies

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.TableMembershipData`. -/
namespace ZkcExamples.Structured.TableMembershipBodies
open Zkc.Source Zkc.Source.Structured


def names : Zkc.Protocols.TableMembership.Source.Names where
  containsDecision := "zkl_eac5bb453765e151a156f69f4baa9e6bcf2f4bd5795339381998b1dec7955769"
  containsStep := "finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_body"
  contains := "zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe"
  queryDecision := "zkl_030ec014d62aacfcdf410a9867a0d256777f66bbad418c7438d2d11c402b4918"
  queryStep := "finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_body"
  membership := "zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98"
  formula := "zkf_39125dccf0dcbcb245fd5a5617424f01d0123f2a50f923aaf33eafa5487b4955"
  containsDomain := "finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_domain"
  membershipDomain := "finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_domain"
  queryName := "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"
  queryConstructor := "case00000000"

abbrev containsDecisionHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.containsDecisionHelper "koala-bear" names

def containsDecisionBody : Region dialect containsDecisionHelper.inputs containsDecisionHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.containsDecisionBody "koala-bear" names

abbrev containsStepHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.containsStepHelper "koala-bear" names

def containsStepBody : Region dialect containsStepHelper.inputs containsStepHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.containsStepBody "koala-bear" names

abbrev containsHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.containsHelper "koala-bear" names

def containsBody : Region dialect containsHelper.inputs containsHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.containsBody "koala-bear" names

abbrev queryDecisionHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.queryDecisionHelper "koala-bear" names

def queryDecisionBody : Region dialect queryDecisionHelper.inputs queryDecisionHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.queryDecisionBody "koala-bear" names

abbrev queryStepHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.queryStepHelper "koala-bear" names

def queryStepBody : Region dialect queryStepHelper.inputs queryStepHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.queryStepBody "koala-bear" names

abbrev membershipHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.membershipHelper "koala-bear" names

def membershipBody : Region dialect membershipHelper.inputs membershipHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.membershipBody "koala-bear" names

abbrev formulaHelper : Helper :=
  Zkc.Protocols.TableMembership.Source.formulaHelper "koala-bear" names

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  Zkc.Protocols.TableMembership.Source.formulaBody "koala-bear" names

abbrev realizationHelper : Helper :=
  ⟨"_mathematical_admission_0", .local, [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def realizationBody : Region dialect realizationHelper.inputs realizationHelper.outputs :=
  .letOp (.invoke {name := "zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98", kind := .math, inputs := [.vector "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev checkMembershipHelper : Helper :=
  ⟨"zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470", .local, [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def checkMembershipBody : Region dialect checkMembershipHelper.inputs checkMembershipHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "_mathematical_admission_0", kind := .local, inputs := [.vector "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

def runSignature : ProtocolSignature where
  name := "zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))]
  outputs := [.boolean]
  inputScopes := [[1], [1]]
  outputScopes := [[1]]

def runBody : Region protocolDialect runSignature.inputs runSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall {name := "zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470", kind := .local, inputs := [.vector "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]} rfl 1 "s0") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.TableMembershipBodies
