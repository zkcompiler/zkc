module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.TableMembershipData`. -/
namespace ZkcExamples.Structured.TableMembershipBodies
open Zkc.Source Zkc.Source.Structured

abbrev containsDecisionHelper : Helper :=
  ⟨"zkl_eac5bb453765e151a156f69f4baa9e6bcf2f4bd5795339381998b1dec7955769", .math, [.boolean, (.field "koala-bear"), (.field "koala-bear")], [.boolean]⟩

def containsDecisionBody : Region dialect containsDecisionHelper.inputs containsDecisionHelper.outputs :=
  .letOp (.fieldEqual "koala-bear") (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp .booleanOr (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev containsStepHelper : Helper :=
  ⟨"finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_body", .math, [.boolean, (.field "koala-bear"), (.vector "koala-bear"), (.field "koala-bear")], [.boolean]⟩

def containsStepBody : Region dialect containsStepHelper.inputs containsStepHelper.outputs :=
  .letOp (.invoke {name := "zkl_eac5bb453765e151a156f69f4baa9e6bcf2f4bd5795339381998b1dec7955769", kind := .math, inputs := [.boolean, .field "koala-bear", .field "koala-bear"], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev containsHelper : Helper :=
  ⟨"zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe", .math, [(.vector "koala-bear"), (.field "koala-bear")], [.boolean]⟩

def containsBody : Region dialect containsHelper.inputs containsHelper.outputs :=
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp (.fold {domain := {name := "finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_domain", inputs := [.vector "koala-bear"], collection := Collection.vector "koala-bear", container := .here, indices := false}, state := [.boolean], captures := [.field "koala-bear"], step := "finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_body", predicate := "", kind := .math}) (.cons (.there .here) (.cons .here (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev queryDecisionHelper : Helper :=
  ⟨"zkl_030ec014d62aacfcdf410a9867a0d256777f66bbad418c7438d2d11c402b4918", .math, [.boolean, .boolean, (.field "koala-bear"), (.vector "koala-bear")], [.boolean]⟩

def queryDecisionBody : Region dialect queryDecisionHelper.inputs queryDecisionHelper.outputs :=
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp .booleanEqual (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.invoke {name := "zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe", kind := .math, inputs := [.vector "koala-bear", .field "koala-bear"], outputs := [.boolean]}) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp .booleanOr (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev queryStepHelper : Helper :=
  ⟨"finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_body", .math, [.boolean, (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil)))), (.vector "koala-bear")], [.boolean]⟩

def queryStepBody : Region dialect queryStepHelper.inputs queryStepHelper.outputs :=
  .letOp (.getProduct "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil)) .boolean .here) (.cons (.there .here) .nil) .nil <|
  .letOp (.getProduct "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil)) (.field "koala-bear") (.there .here)) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.invoke {name := "zkl_030ec014d62aacfcdf410a9867a0d256777f66bbad418c7438d2d11c402b4918", kind := .math, inputs := [.boolean, .boolean, .field "koala-bear", .vector "koala-bear"], outputs := [.boolean]}) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev membershipHelper : Helper :=
  ⟨"zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98", .math, [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def membershipBody : Region dialect membershipHelper.inputs membershipHelper.outputs :=
  .letOp (.booleanConstant true) .nil .nil <|
  .letOp (.fold {domain := {name := "finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_domain", inputs := [(.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], collection := Collection.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))), container := .here, indices := false}, state := [.boolean], captures := [.vector "koala-bear"], step := "finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_body", predicate := "", kind := .math}) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev realizationHelper : Helper :=
  ⟨"zkl_realization_6e6753342f25cfa4f16973f68e74cc7f7748a3c5ba000bde2a77837d3ab18307", .local, [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def realizationBody : Region dialect realizationHelper.inputs realizationHelper.outputs :=
  .letOp (.invoke {name := "zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98", kind := .math, inputs := [.vector "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper :=
  ⟨"zkf_39125dccf0dcbcb245fd5a5617424f01d0123f2a50f923aaf33eafa5487b4955", .math, [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.invoke {name := "zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98", kind := .math, inputs := [.vector "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev checkMembershipHelper : Helper :=
  ⟨"zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470", .local, [(.vector "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons .boolean (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def checkMembershipBody : Region dialect checkMembershipHelper.inputs checkMembershipHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_realization_6e6753342f25cfa4f16973f68e74cc7f7748a3c5ba000bde2a77837d3ab18307", kind := .local, inputs := [.vector "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons .boolean (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
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
