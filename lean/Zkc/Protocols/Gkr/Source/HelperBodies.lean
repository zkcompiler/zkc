module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

set_option autoImplicit false

/-! Retained GKR helper templates. Source clients associate their actual full
signatures and raw bodies with these trees; names alone supply no laws. -/
namespace Zkc.Protocols.Gkr.Source.HelperBodies
open Zkc.Source Zkc.Source.Structured

abbrev firstInterpolationMapHelper : Helper :=
  ⟨"_finite_admission_1", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def firstInterpolationMapBody : Region dialect firstInterpolationMapHelper.inputs firstInterpolationMapHelper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev prefixRestrictionHelper : Helper :=
  ⟨"_finite_admission_3", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

abbrev tableValuesHelper : Helper :=
  ⟨"_mathematical_admission_0", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

abbrev sumHelper : Helper :=
  ⟨"zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def sumBody : Region dialect sumHelper.inputs sumHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev evaluateHelper : Helper :=
  ⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateBody : Region dialect evaluateHelper.inputs evaluateHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_0", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev evaluateWiringHelper : Helper :=
  ⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateWiringBody : Region dialect evaluateWiringHelper.inputs evaluateWiringHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)))) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_0", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev interpolateHelper : Helper :=
  ⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateBody : Region dialect interpolateHelper.inputs interpolateHelper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev lineInterpolationRealizationHelper : Helper :=
  ⟨"_mathematical_admission_14", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def lineInterpolationRealizationBody : Region dialect lineInterpolationRealizationHelper.inputs lineInterpolationRealizationHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev lineCallbackHelper : Helper :=
  ⟨"zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def lineCallbackBody : Region dialect lineCallbackHelper.inputs lineCallbackHelper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_14", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev lineInterpolationMapHelper : Helper :=
  ⟨"_finite_admission_25", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def lineInterpolationMapBody : Region dialect lineInterpolationMapHelper.inputs lineInterpolationMapHelper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev linePointHelper : Helper :=
  ⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def linePointBody : Region dialect linePointHelper.inputs linePointHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_25", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev powerStepHelper : Helper :=
  ⟨"zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerStepBody : Region dialect powerStepHelper.inputs powerStepHelper.outputs :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there .here) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev powerStepRealizationHelper : Helper :=
  ⟨"_mathematical_admission_27", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerStepRealizationBody : Region dialect powerStepRealizationHelper.inputs powerStepRealizationHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev powerStepWrapperHelper : Helper :=
  ⟨"zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerStepWrapperBody : Region dialect powerStepWrapperHelper.inputs powerStepWrapperHelper.outputs :=
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_27", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev powerFoldCallbackHelper : Helper :=
  ⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerFoldCallbackBody : Region dialect powerFoldCallbackHelper.inputs powerFoldCallbackHelper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev powerInitialStateHelper : Helper :=
  ⟨"zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", .math, [], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerInitialStateBody : Region dialect powerInitialStateHelper.inputs powerInitialStateHelper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fieldConstant "bls12-381.fr" 1) .nil .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev powerInitialRealizationHelper : Helper :=
  ⟨"_mathematical_admission_26", .local, [], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerInitialRealizationBody : Region dialect powerInitialRealizationHelper.inputs powerInitialRealizationHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", .math, [], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev powerFoldHelper : Helper :=
  ⟨"_finite_admission_28", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerFoldBody : Region dialect powerFoldHelper.inputs powerFoldHelper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")], "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev powerFoldWrapperHelper : Helper :=
  ⟨"zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def powerFoldWrapperBody : Region dialect powerFoldWrapperHelper.inputs powerFoldWrapperHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_28", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev evaluateCoefficientsHelper : Helper :=
  ⟨"zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateCoefficientsBody : Region dialect evaluateCoefficientsHelper.inputs evaluateCoefficientsHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_26", .local, [], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev powerOfTwoHelper : Helper :=
  ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩

def powerOfTwoBody : Region dialect powerOfTwoHelper.inputs powerOfTwoHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) .nil))) (.cons (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.indexConstant 2)) .nil .nil (.letOp (.mark "s5") .nil .nil (.letOp (.exec .indexMul) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) <|
  .ret (.cons .here .nil)

abbrev selectBlockHelper : Helper :=
  ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def selectBlockBody : Region dialect selectBlockHelper.inputs selectBlockHelper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.loop [(.vector "bls12-381.fr"), .index] [.index]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))))) (.cons (.letOp (.mark "s5") .nil .nil (.letOp (.exec (.indexConstant 1)) .nil .nil (.letOp (.mark "s6") .nil .nil (.letOp (.exec .indexSub) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s8") .nil .nil (.letOp (.invoke (⟨ "s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index] ⟩ : Helper)) (.cons .here .nil) .nil (.letOp (.mark "s9") .nil .nil (.letOp (.exec .indexDiv) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil (.letOp (.mark "s10") .nil .nil (.letOp (.exec (.indexConstant 2)) .nil .nil (.letOp (.mark "s11") .nil .nil (.letOp (.exec .indexMod) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "s13") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil (.letOp (.mark "s15") .nil .nil (.letOp (.exec (.indexConstant 1)) .nil .nil (.letOp (.mark "s16") .nil .nil (.letOp (.exec .indexEqual) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s19") .nil .nil (.letOp (.branch [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] [(.vector "bls12-381.fr")]) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) (.cons (.ret (.cons (.there .here) .nil)) (.cons (.ret (.cons .here .nil)) .nil)) (.ret (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))))))))))))))))))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev interpolateRealizationHelper : Helper :=
  ⟨"_mathematical_admission_2", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateRealizationBody : Region dialect interpolateRealizationHelper.inputs interpolateRealizationHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

/-- Complete round protocol ABI; the admitted declaration chooses its nominal name. -/
def roundsProtocolSignature (name : String) : ProtocolSignature where
  name := name
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
  outputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [0], [1], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [0], [0], [0], [1], [1]]

/-- One exact typed round callback, shared by source selection and normalization. -/
def roundsCallbackBody : Region protocolDialect
    [.index, .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr",
      .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr",
      .field "bls12-381.fr", .service "random.bls12-381.fr/0"]
    (roundsProtocolSignature "").outputs :=
  (.letOp (.mark "s10") .nil .nil (.letOp (.localCall (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl 0 "s10") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil (.letOp (.mark "label_726f756e64_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_726f756e64_1") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_726f756e64_2") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_2") (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "s21") .nil .nil (.letOp (.guard 1 "s21") (.cons .here .nil) .nil (.letOp (.mark "label_6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil) .nil (.letOp (.mark "label_64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "s26") .nil .nil (.letOp (.localCall (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) rfl 0 "s26") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons .here .nil))))) .nil (.letOp (.mark "s28") .nil .nil (.letOp (.localCall (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl 0 "s28") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.mark "s30") .nil .nil (.letOp (.localCall (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) rfl 1 "s30") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons .here .nil)) .nil (.ret (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Source template with an arbitrary operational maximum. The selected source
entry must associate to this complete tree, including its callback and helper calls. -/
def roundsProtocolBody (maximum : Nat) : Region protocolDialect
    (roundsProtocolSignature "").inputs (roundsProtocolSignature "").outputs :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s1") .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s3") (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.repeat (⟨ [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], maximum⟩ : RepeatSpec) "s9") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil))))))))) (.cons roundsCallbackBody .nil) <|
  .letOp (.mark "s42") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s42") (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there .here) .nil)))))))

end Zkc.Protocols.Gkr.Source.HelperBodies
