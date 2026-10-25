module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
public import Zkc.Protocols.AlgebraicRounds.Gate

@[expose] public section

/-! Generated actual-helper gate equations. This is not a full GKR theorem. -/
namespace ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open Zkc.Protocols.AlgebraicRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev emptyDefinition : CheckedDefinition := payload.definitions.get ⟨0, by decide +kernel⟩
abbrev emptyHelper : Helper := (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper)
def emptyBody : Region dialect emptyHelper.inputs emptyHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil (.ret (.cons .here .nil))))
theorem empty_closed (args : Values (assignment F G) emptyHelper.inputs) :
    invoke (helpers payload).closed emptyHelper args =
      emptyBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    emptyDefinition (List.get_mem _ _) (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) rfl emptyBody rfl args

abbrev appendDefinition : CheckedDefinition := payload.definitions.get ⟨1, by decide +kernel⟩
abbrev appendHelper : Helper := (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def appendBody : Region dialect appendHelper.inputs appendHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))))
theorem append_closed (args : Values (assignment F G) appendHelper.inputs) :
    invoke (helpers payload).closed appendHelper args =
      appendBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    appendDefinition (List.get_mem _ _) (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl appendBody rfl args

abbrev gateValueDefinition : CheckedDefinition := payload.definitions.get ⟨31, by decide +kernel⟩
abbrev gateValueHelper : Helper := (⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateValueBody : Region dialect gateValueHelper.inputs gateValueHelper.outputs :=
  (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))
theorem gateValue_closed (args : Values (assignment F G) gateValueHelper.inputs) :
    invoke (helpers payload).closed gateValueHelper args =
      gateValueBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    gateValueDefinition (List.get_mem _ _) (⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateValueBody rfl args

abbrev gateValuesDefinition : CheckedDefinition := payload.definitions.get ⟨32, by decide +kernel⟩
abbrev gateValuesHelper : Helper := (⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def gateValuesBody : Region dialect gateValuesHelper.inputs gateValuesHelper.outputs :=
  (.letOp (.map ⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", "bls12-381.fr", [true, true, true, true]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil (.ret (.cons .here .nil)))
theorem gateValues_closed (args : Values (assignment F G) gateValuesHelper.inputs) :
    invoke (helpers payload).closed gateValuesHelper args =
      gateValuesBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    gateValuesDefinition (List.get_mem _ _) (⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl gateValuesBody rfl args

abbrev gateQuadraticDefinition : CheckedDefinition := payload.definitions.get ⟨37, by decide +kernel⟩
abbrev gateQuadraticHelper : Helper := (⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def gateQuadraticBody : Region dialect gateQuadraticHelper.inputs gateQuadraticHelper.outputs :=
  (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))))))))))))
theorem gateQuadratic_closed (args : Values (assignment F G) gateQuadraticHelper.inputs) :
    invoke (helpers payload).closed gateQuadraticHelper args =
      gateQuadraticBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    gateQuadraticDefinition (List.get_mem _ _) (⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl gateQuadraticBody rfl args

abbrev gateQuadraticsDefinition : CheckedDefinition := payload.definitions.get ⟨38, by decide +kernel⟩
abbrev gateQuadraticsHelper : Helper := (⟨"zkl_map_c924eca691a9f196c01671f2b9eb9f861c0eea9093f77c8c7fbeabb112d1de13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def gateQuadraticsBody : Region dialect gateQuadraticsHelper.inputs gateQuadraticsHelper.outputs :=
  (.letOp (.map ⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", "bls12-381.fr", [true, true, true, true, true, true, true, true]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil (.ret (.cons .here .nil)))
theorem gateQuadratics_closed (args : Values (assignment F G) gateQuadraticsHelper.inputs) :
    invoke (helpers payload).closed gateQuadraticsHelper args =
      gateQuadraticsBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    gateQuadraticsDefinition (List.get_mem _ _) (⟨"zkl_map_c924eca691a9f196c01671f2b9eb9f861c0eea9093f77c8c7fbeabb112d1de13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl gateQuadraticsBody rfl args

abbrev linearCoefficientDefinition : CheckedDefinition := payload.definitions.get ⟨39, by decide +kernel⟩
abbrev linearCoefficientHelper : Helper := (⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def linearCoefficientBody : Region dialect linearCoefficientHelper.inputs linearCoefficientHelper.outputs :=
  (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.ret (.cons .here .nil))))
theorem linearCoefficient_closed (args : Values (assignment F G) linearCoefficientHelper.inputs) :
    invoke (helpers payload).closed linearCoefficientHelper args =
      linearCoefficientBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    linearCoefficientDefinition (List.get_mem _ _) (⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl linearCoefficientBody rfl args

abbrev linearWrapperDefinition : CheckedDefinition := payload.definitions.get ⟨40, by decide +kernel⟩
abbrev linearWrapperHelper : Helper := (⟨"zkl_realization_4077daa8d30ef9f9ed0f8a89f7e3c731a33fa91da5e56301c22d3f8aab9de4bb", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def linearWrapperBody : Region dialect linearWrapperHelper.inputs linearWrapperHelper.outputs :=
  (.letOp (.invoke (⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))
theorem linearWrapper_closed (args : Values (assignment F G) linearWrapperHelper.inputs) :
    invoke (helpers payload).closed linearWrapperHelper args =
      linearWrapperBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    linearWrapperDefinition (List.get_mem _ _) (⟨"zkl_realization_4077daa8d30ef9f9ed0f8a89f7e3c731a33fa91da5e56301c22d3f8aab9de4bb", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl linearWrapperBody rfl args

abbrev roundMessageDefinition : CheckedDefinition := payload.definitions.get ⟨41, by decide +kernel⟩
abbrev roundMessageHelper : Helper := (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def roundMessageBody : Region dialect roundMessageHelper.inputs roundMessageHelper.outputs :=
  (.letOp (.mark "s1") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "s7") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil (.letOp (.mark "s10") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) .nil (.letOp (.mark "s16") .nil .nil (.letOp (.invoke (⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil)))) .nil (.letOp (.mark "s17") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s23") .nil .nil (.letOp (.invoke (⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)))) .nil (.letOp (.mark "s24") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s34") .nil .nil (.letOp (.invoke (⟨"zkl_map_c924eca691a9f196c01671f2b9eb9f861c0eea9093f77c8c7fbeabb112d1de13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))))) .nil (.letOp (.mark "s35") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s37") .nil .nil (.letOp (.invoke (⟨"zkl_realization_4077daa8d30ef9f9ed0f8a89f7e3c731a33fa91da5e56301c22d3f8aab9de4bb", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil))) .nil (.ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there .here) .nil))))))))))))))))))))))))))
theorem roundMessage_closed (args : Values (assignment F G) roundMessageHelper.inputs) :
    invoke (helpers payload).closed roundMessageHelper args =
      roundMessageBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    roundMessageDefinition (List.get_mem _ _) (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl roundMessageBody rfl args

abbrev interpolationDefinition : CheckedDefinition := payload.definitions.get ⟨42, by decide +kernel⟩
abbrev interpolationHelper : Helper := (⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def interpolationBody : Region dialect interpolationHelper.inputs interpolationHelper.outputs :=
  (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))
theorem interpolation_closed (args : Values (assignment F G) interpolationHelper.inputs) :
    invoke (helpers payload).closed interpolationHelper args =
      interpolationBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    interpolationDefinition (List.get_mem _ _) (⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) rfl interpolationBody rfl args

abbrev interpolationsDefinition : CheckedDefinition := payload.definitions.get ⟨43, by decide +kernel⟩
abbrev interpolationsHelper : Helper := (⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def interpolationsBody : Region dialect interpolationsHelper.inputs interpolationsHelper.outputs :=
  (.letOp (.map ⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", "bls12-381.fr", [true, true, false]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))
theorem interpolations_closed (args : Values (assignment F G) interpolationsHelper.inputs) :
    invoke (helpers payload).closed interpolationsHelper args =
      interpolationsBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    interpolationsDefinition (List.get_mem _ _) (⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl interpolationsBody rfl args

abbrev factorRestrictionDefinition : CheckedDefinition := payload.definitions.get ⟨44, by decide +kernel⟩
abbrev factorRestrictionHelper : Helper := (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)
def factorRestrictionBody : Region dialect factorRestrictionHelper.inputs factorRestrictionHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s4") .nil .nil (.letOp (.invoke (⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil (.ret (.cons .here .nil))))))
theorem factorRestriction_closed (args : Values (assignment F G) factorRestrictionHelper.inputs) :
    invoke (helpers payload).closed factorRestrictionHelper args =
      factorRestrictionBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    factorRestrictionDefinition (List.get_mem _ _) (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl factorRestrictionBody rfl args

abbrev gateRestrictionDefinition : CheckedDefinition := payload.definitions.get ⟨45, by decide +kernel⟩
abbrev gateRestrictionHelper : Helper := (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper)
def gateRestrictionBody : Region dialect gateRestrictionHelper.inputs gateRestrictionHelper.outputs :=
  (.letOp (.mark "s1") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.mark "s3") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil (.letOp (.mark "s5") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "s7") .nil .nil (.letOp (.invoke (⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)))))))))))))
theorem gateRestriction_closed (args : Values (assignment F G) gateRestrictionHelper.inputs) :
    invoke (helpers payload).closed gateRestrictionHelper args =
      gateRestrictionBody.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=
  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked
    gateRestrictionDefinition (List.get_mem _ _) (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) rfl gateRestrictionBody rfl args

abbrev valueDefinition : CheckedDefinition := payload.definitions.get ⟨31, by decide +kernel⟩

theorem value_body (add mul left right : F) :
    valueDefinition.body.component
      (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed)
      (Evaluation.componentOperation (.silent _) (helpers payload)) (((.cons (some add) (.cons (some mul) (.cons (some left) (.cons (some right) .nil)))) : Values (Component (assignment F G)) valueDefinition.inputs).get) =
      .done (.cons (some (Gate.value add mul left right)) .nil) := by
  kernel_rfl

theorem value_invoke (add mul left right : F) :
    invoke (helpers (F := F) (G := G) payload).components valueDefinition.helper (.cons (some add) (.cons (some mul) (.cons (some left) (.cons (some right) .nil)))) =
      .done (.cons (some (Gate.value add mul left right)) .nil) :=
  (helper_body payload valueDefinition (List.get_mem _ _) (.cons (some add) (.cons (some mul) (.cons (some left) (.cons (some right) .nil))))).trans
    (value_body add mul left right)

abbrev quadraticDefinition : CheckedDefinition := payload.definitions.get ⟨37, by decide +kernel⟩

theorem quadratic_body (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    quadraticDefinition.body.component
      (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed)
      (Evaluation.componentOperation (.silent _) (helpers payload)) (((.cons (some a0) (.cons (some a1) (.cons (some m0) (.cons (some m1) (.cons (some l0) (.cons (some l1) (.cons (some r0) (.cons (some r1) .nil)))))))) : Values (Component (assignment F G)) quadraticDefinition.inputs).get) =
      .done (.cons (some (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1)) .nil) := by
  kernel_rfl

theorem quadratic_invoke (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    invoke (helpers (F := F) (G := G) payload).components quadraticDefinition.helper (.cons (some a0) (.cons (some a1) (.cons (some m0) (.cons (some m1) (.cons (some l0) (.cons (some l1) (.cons (some r0) (.cons (some r1) .nil)))))))) =
      .done (.cons (some (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1)) .nil) :=
  (helper_body payload quadraticDefinition (List.get_mem _ _) (.cons (some a0) (.cons (some a1) (.cons (some m0) (.cons (some m1) (.cons (some l0) (.cons (some l1) (.cons (some r0) (.cons (some r1) .nil))))))))).trans
    (quadratic_body a0 a1 m0 m1 l0 l1 r0 r1)

end
end ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
