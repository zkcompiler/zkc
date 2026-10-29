module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks

@[expose] public section

/-! Generated actual-helper gate equations. This is not a full GKR theorem. -/
namespace ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev roundsOpenDefinition : CheckedDefinition := payload.definitions.get ⟨22, by decide +kernel⟩
abbrev roundsOpenHelper : Helper := (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def roundsOpenBody : Region dialect roundsOpenHelper.inputs roundsOpenHelper.outputs :=
  (.ret (.cons .here (.cons (.there .here) .nil)))
theorem roundsOpen_closed (args : Values (assignment F G) roundsOpenHelper.inputs) :
    invoke ((helpers payload).closed) roundsOpenHelper args =
      roundsOpenBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    roundsOpenDefinition (List.get_mem _ _) (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl roundsOpenBody rfl args

abbrev roundsCloseDefinition : CheckedDefinition := payload.definitions.get ⟨26, by decide +kernel⟩
abbrev roundsCloseHelper : Helper := (⟨"zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def roundsCloseBody : Region dialect roundsCloseHelper.inputs roundsCloseHelper.outputs :=
  (.ret (.cons .here (.cons (.there .here) .nil)))
theorem roundsClose_closed (args : Values (assignment F G) roundsCloseHelper.inputs) :
    invoke ((helpers payload).closed) roundsCloseHelper args =
      roundsCloseBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    roundsCloseDefinition (List.get_mem _ _) (⟨"zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl roundsCloseBody rfl args

abbrev layerOpenDefinition : CheckedDefinition := payload.definitions.get ⟨12, by decide +kernel⟩
abbrev layerOpenHelper : Helper := (⟨"zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def layerOpenBody : Region dialect layerOpenHelper.inputs layerOpenHelper.outputs :=
  (.ret (.cons .here (.cons (.there .here) .nil)))
theorem layerOpen_closed (args : Values (assignment F G) layerOpenHelper.inputs) :
    invoke ((helpers payload).closed) layerOpenHelper args =
      layerOpenBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    layerOpenDefinition (List.get_mem _ _) (⟨"zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl layerOpenBody rfl args

abbrev pendingDefinition : CheckedDefinition := payload.definitions.get ⟨20, by decide +kernel⟩
abbrev pendingHelper : Helper := (⟨"zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def pendingBody : Region dialect pendingHelper.inputs pendingHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil (.ret (.cons .here (.cons (.there .here) .nil)))))
theorem pending_closed (args : Values (assignment F G) pendingHelper.inputs) :
    invoke ((helpers payload).closed) pendingHelper args =
      pendingBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    pendingDefinition (List.get_mem _ _) (⟨"zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl pendingBody rfl args

abbrev emptyDefinition : CheckedDefinition := payload.definitions.get ⟨5, by decide +kernel⟩
abbrev emptyHelper : Helper := (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper)
def emptyBody : Region dialect emptyHelper.inputs emptyHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil (.ret (.cons .here .nil))))
theorem empty_closed (args : Values (assignment F G) emptyHelper.inputs) :
    invoke ((helpers payload).closed) emptyHelper args =
      emptyBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    emptyDefinition (List.get_mem _ _) (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) rfl emptyBody rfl args

abbrev appendDefinition : CheckedDefinition := payload.definitions.get ⟨6, by decide +kernel⟩
abbrev appendHelper : Helper := (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def appendBody : Region dialect appendHelper.inputs appendHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))))
theorem append_closed (args : Values (assignment F G) appendHelper.inputs) :
    invoke ((helpers payload).closed) appendHelper args =
      appendBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    appendDefinition (List.get_mem _ _) (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl appendBody rfl args

abbrev gateValueDefinition : CheckedDefinition := payload.definitions.get ⟨19, by decide +kernel⟩
abbrev gateValueHelper : Helper := (⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateValueBody : Region dialect gateValueHelper.inputs gateValueHelper.outputs :=
  (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))
theorem gateValue_closed (args : Values (assignment F G) gateValueHelper.inputs) :
    invoke ((helpers payload).closed) gateValueHelper args =
      gateValueBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateValueDefinition (List.get_mem _ _) (⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateValueBody rfl args

abbrev gateValuesLeftDefinition : CheckedDefinition := payload.definitions.get ⟨66, by decide +kernel⟩
abbrev gateValuesLeftHelper : Helper := (⟨"_finite_admission_8", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def gateValuesLeftBody : Region dialect gateValuesLeftHelper.inputs gateValuesLeftHelper.outputs :=
  (.letOp (.collect ⟨⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))))))⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil (.ret (.cons .here .nil)))
theorem gateValuesLeft_closed (args : Values (assignment F G) gateValuesLeftHelper.inputs) :
    invoke ((helpers payload).closed) gateValuesLeftHelper args =
      gateValuesLeftBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateValuesLeftDefinition (List.get_mem _ _) (⟨"_finite_admission_8", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl gateValuesLeftBody rfl args

abbrev gateValuesLeftCollection : CollectSpec :=
  ⟨⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))))))⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩

abbrev gateValuesRightDefinition : CheckedDefinition := payload.definitions.get ⟨67, by decide +kernel⟩
abbrev gateValuesRightHelper : Helper := (⟨"_finite_admission_9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def gateValuesRightBody : Region dialect gateValuesRightHelper.inputs gateValuesRightHelper.outputs :=
  (.letOp (.collect ⟨⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))))))⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil (.ret (.cons .here .nil)))
theorem gateValuesRight_closed (args : Values (assignment F G) gateValuesRightHelper.inputs) :
    invoke ((helpers payload).closed) gateValuesRightHelper args =
      gateValuesRightBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateValuesRightDefinition (List.get_mem _ _) (⟨"_finite_admission_9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl gateValuesRightBody rfl args

abbrev gateValuesRightCollection : CollectSpec :=
  ⟨⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))))))⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩

abbrev gateValueCallbackDefinition : CheckedDefinition := payload.definitions.get ⟨55, by decide +kernel⟩
abbrev gateValueCallbackHelper : Helper := (⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateValueCallbackBody : Region dialect gateValueCallbackHelper.inputs gateValueCallbackHelper.outputs :=
  (.letOp (.mark "body") .nil .nil (.letOp (.invoke (⟨"_mathematical_admission_5", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil (.ret (.cons .here .nil))))
theorem gateValueCallback_closed (args : Values (assignment F G) gateValueCallbackHelper.inputs) :
    invoke ((helpers payload).closed) gateValueCallbackHelper args =
      gateValueCallbackBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateValueCallbackDefinition (List.get_mem _ _) (⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateValueCallbackBody rfl args

abbrev gateValueRealizationDefinition : CheckedDefinition := payload.definitions.get ⟨54, by decide +kernel⟩
abbrev gateValueRealizationHelper : Helper := (⟨"_mathematical_admission_5", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateValueRealizationBody : Region dialect gateValueRealizationHelper.inputs gateValueRealizationHelper.outputs :=
  (.letOp (.invoke (⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil (.ret (.cons .here .nil)))
theorem gateValueRealization_closed (args : Values (assignment F G) gateValueRealizationHelper.inputs) :
    invoke ((helpers payload).closed) gateValueRealizationHelper args =
      gateValueRealizationBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateValueRealizationDefinition (List.get_mem _ _) (⟨"_mathematical_admission_5", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateValueRealizationBody rfl args

abbrev gateQuadraticDefinition : CheckedDefinition := payload.definitions.get ⟨23, by decide +kernel⟩
abbrev gateQuadraticHelper : Helper := (⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateQuadraticBody : Region dialect gateQuadraticHelper.inputs gateQuadraticHelper.outputs :=
  (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))))))))))))
theorem gateQuadratic_closed (args : Values (assignment F G) gateQuadraticHelper.inputs) :
    invoke ((helpers payload).closed) gateQuadraticHelper args =
      gateQuadraticBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateQuadraticDefinition (List.get_mem _ _) (⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateQuadraticBody rfl args

abbrev gateQuadraticsDefinition : CheckedDefinition := payload.definitions.get ⟨71, by decide +kernel⟩
abbrev gateQuadraticsHelper : Helper := (⟨"_finite_admission_10", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def gateQuadraticsBody : Region dialect gateQuadraticsHelper.inputs gateQuadraticsHelper.outputs :=
  (.letOp (.collect ⟨⟨"zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there .here))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there .here)))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there (.there .here))))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))))))))))))))⟩, (.vector "bls12-381.fr"), [], "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil (.ret (.cons .here .nil)))
theorem gateQuadratics_closed (args : Values (assignment F G) gateQuadraticsHelper.inputs) :
    invoke ((helpers payload).closed) gateQuadraticsHelper args =
      gateQuadraticsBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateQuadraticsDefinition (List.get_mem _ _) (⟨"_finite_admission_10", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl gateQuadraticsBody rfl args

abbrev gateQuadraticsCollection : CollectSpec :=
  ⟨⟨"zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there .here))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there .here)))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there (.there .here))))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))))))))))))))⟩, (.vector "bls12-381.fr"), [], "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", "", .local⟩

abbrev gateQuadraticCallbackDefinition : CheckedDefinition := payload.definitions.get ⟨70, by decide +kernel⟩
abbrev gateQuadraticCallbackHelper : Helper := (⟨"zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateQuadraticCallbackBody : Region dialect gateQuadraticCallbackHelper.inputs gateQuadraticCallbackHelper.outputs :=
  (.letOp (.mark "body") .nil .nil (.letOp (.invoke (⟨"_mathematical_admission_12", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil (.ret (.cons .here .nil))))
theorem gateQuadraticCallback_closed (args : Values (assignment F G) gateQuadraticCallbackHelper.inputs) :
    invoke ((helpers payload).closed) gateQuadraticCallbackHelper args =
      gateQuadraticCallbackBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateQuadraticCallbackDefinition (List.get_mem _ _) (⟨"zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateQuadraticCallbackBody rfl args

abbrev gateQuadraticRealizationDefinition : CheckedDefinition := payload.definitions.get ⟨69, by decide +kernel⟩
abbrev gateQuadraticRealizationHelper : Helper := (⟨"_mathematical_admission_12", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateQuadraticRealizationBody : Region dialect gateQuadraticRealizationHelper.inputs gateQuadraticRealizationHelper.outputs :=
  (.letOp (.invoke (⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil (.ret (.cons .here .nil)))
theorem gateQuadraticRealization_closed (args : Values (assignment F G) gateQuadraticRealizationHelper.inputs) :
    invoke ((helpers payload).closed) gateQuadraticRealizationHelper args =
      gateQuadraticRealizationBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateQuadraticRealizationDefinition (List.get_mem _ _) (⟨"_mathematical_admission_12", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateQuadraticRealizationBody rfl args

abbrev linearCoefficientDefinition : CheckedDefinition := payload.definitions.get ⟨24, by decide +kernel⟩
abbrev linearCoefficientHelper : Helper := (⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def linearCoefficientBody : Region dialect linearCoefficientHelper.inputs linearCoefficientHelper.outputs :=
  (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.ret (.cons .here .nil))))
theorem linearCoefficient_closed (args : Values (assignment F G) linearCoefficientHelper.inputs) :
    invoke ((helpers payload).closed) linearCoefficientHelper args =
      linearCoefficientBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    linearCoefficientDefinition (List.get_mem _ _) (⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl linearCoefficientBody rfl args

abbrev linearWrapperDefinition : CheckedDefinition := payload.definitions.get ⟨68, by decide +kernel⟩
abbrev linearWrapperHelper : Helper := (⟨"_mathematical_admission_11", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def linearWrapperBody : Region dialect linearWrapperHelper.inputs linearWrapperHelper.outputs :=
  (.letOp (.invoke (⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))
theorem linearWrapper_closed (args : Values (assignment F G) linearWrapperHelper.inputs) :
    invoke ((helpers payload).closed) linearWrapperHelper args =
      linearWrapperBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    linearWrapperDefinition (List.get_mem _ _) (⟨"_mathematical_admission_11", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl linearWrapperBody rfl args

abbrev roundMessageDefinition : CheckedDefinition := payload.definitions.get ⟨72, by decide +kernel⟩
abbrev roundMessageHelper : Helper := (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def roundMessageBody : Region dialect roundMessageHelper.inputs roundMessageHelper.outputs :=
  (.letOp (.mark "s1") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "s7") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil (.letOp (.mark "s10") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) .nil (.letOp (.mark "s16") .nil .nil (.letOp (.invoke (⟨"_finite_admission_8", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil)))) .nil (.letOp (.mark "s17") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s23") .nil .nil (.letOp (.invoke (⟨"_finite_admission_9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)))) .nil (.letOp (.mark "s24") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s34") .nil .nil (.letOp (.invoke (⟨"_finite_admission_10", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))))) .nil (.letOp (.mark "s35") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s37") .nil .nil (.letOp (.invoke (⟨"_mathematical_admission_11", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil))) .nil (.ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there .here) .nil))))))))))))))))))))))))))
theorem roundMessage_closed (args : Values (assignment F G) roundMessageHelper.inputs) :
    invoke ((helpers payload).closed) roundMessageHelper args =
      roundMessageBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    roundMessageDefinition (List.get_mem _ _) (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl roundMessageBody rfl args

abbrev interpolationDefinition : CheckedDefinition := payload.definitions.get ⟨25, by decide +kernel⟩
abbrev interpolationHelper : Helper := (⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def interpolationBody : Region dialect interpolationHelper.inputs interpolationHelper.outputs :=
  (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))
theorem interpolation_closed (args : Values (assignment F G) interpolationHelper.inputs) :
    invoke ((helpers payload).closed) interpolationHelper args =
      interpolationBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    interpolationDefinition (List.get_mem _ _) (⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl interpolationBody rfl args

abbrev interpolationsDefinition : CheckedDefinition := payload.definitions.get ⟨75, by decide +kernel⟩
abbrev interpolationsHelper : Helper := (⟨"_finite_admission_13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def interpolationsBody : Region dialect interpolationsHelper.inputs interpolationsHelper.outputs :=
  (.letOp (.collect ⟨⟨"zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))
theorem interpolations_closed (args : Values (assignment F G) interpolationsHelper.inputs) :
    invoke ((helpers payload).closed) interpolationsHelper args =
      interpolationsBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    interpolationsDefinition (List.get_mem _ _) (⟨"_finite_admission_13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl interpolationsBody rfl args

abbrev interpolationsCollection : CollectSpec :=
  ⟨⟨"zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here))))⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", "", .local⟩

abbrev interpolationCallbackDefinition : CheckedDefinition := payload.definitions.get ⟨74, by decide +kernel⟩
abbrev interpolationCallbackHelper : Helper := (⟨"zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def interpolationCallbackBody : Region dialect interpolationCallbackHelper.inputs interpolationCallbackHelper.outputs :=
  (.letOp (.mark "body") .nil .nil (.letOp (.invoke (⟨"_mathematical_admission_14", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil (.ret (.cons .here .nil))))
theorem interpolationCallback_closed (args : Values (assignment F G) interpolationCallbackHelper.inputs) :
    invoke ((helpers payload).closed) interpolationCallbackHelper args =
      interpolationCallbackBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    interpolationCallbackDefinition (List.get_mem _ _) (⟨"zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl interpolationCallbackBody rfl args

abbrev interpolationRealizationDefinition : CheckedDefinition := payload.definitions.get ⟨73, by decide +kernel⟩
abbrev interpolationRealizationHelper : Helper := (⟨"_mathematical_admission_14", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def interpolationRealizationBody : Region dialect interpolationRealizationHelper.inputs interpolationRealizationHelper.outputs :=
  (.letOp (.invoke (⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))
theorem interpolationRealization_closed (args : Values (assignment F G) interpolationRealizationHelper.inputs) :
    invoke ((helpers payload).closed) interpolationRealizationHelper args =
      interpolationRealizationBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    interpolationRealizationDefinition (List.get_mem _ _) (⟨"_mathematical_admission_14", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl interpolationRealizationBody rfl args

abbrev factorRestrictionDefinition : CheckedDefinition := payload.definitions.get ⟨76, by decide +kernel⟩
abbrev factorRestrictionHelper : Helper := (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def factorRestrictionBody : Region dialect factorRestrictionHelper.inputs factorRestrictionHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s4") .nil .nil (.letOp (.invoke (⟨"_finite_admission_13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil (.ret (.cons .here .nil))))))
theorem factorRestriction_closed (args : Values (assignment F G) factorRestrictionHelper.inputs) :
    invoke ((helpers payload).closed) factorRestrictionHelper args =
      factorRestrictionBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    factorRestrictionDefinition (List.get_mem _ _) (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl factorRestrictionBody rfl args

abbrev gateRestrictionDefinition : CheckedDefinition := payload.definitions.get ⟨77, by decide +kernel⟩
abbrev gateRestrictionHelper : Helper := (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper)
def gateRestrictionBody : Region dialect gateRestrictionHelper.inputs gateRestrictionHelper.outputs :=
  (.letOp (.mark "s1") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.mark "s3") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil (.letOp (.mark "s5") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "s7") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)))))))))))))
theorem gateRestriction_closed (args : Values (assignment F G) gateRestrictionHelper.inputs) :
    invoke ((helpers payload).closed) gateRestrictionHelper args =
      gateRestrictionBody.denote (Evaluation.meaning (.silent (participantInterface F G)) ((helpers payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent (participantInterface F G)) payload.definitions payload.linked
    gateRestrictionDefinition (List.get_mem _ _) (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) rfl gateRestrictionBody rfl args

end
end ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
