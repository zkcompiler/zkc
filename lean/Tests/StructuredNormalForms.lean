import Zkc.Source.Structured.NormalForm.Check
import ZkcExamples.Structured.ChaumPedersenNormalForms
import ZkcExamples.Structured.SumcheckRoundNormalForms

/-! Controls for the normalizer and the form checker. The migrated generated
modules are the positive controls; these cases show that the kernel refuses
a form literal that is not the normalizer's result, that the normalizer
refuses what is outside its fragment by name, and that the checker accepts
the generated form and refuses one that misstates an action. -/
set_option autoImplicit false
namespace Tests.StructuredNormalForms
open Zkc.Source Zkc.Source.Structured NormalForm ZkcExamples.Structured

/-- The verifier's form with the challenge sent to the response's site. -/
noncomputable def misdirected : Form [] ChaumPedersenNormalForms.verifierPattern.scope
    ChaumPedersenViews.program.payload.entry.outputs :=
  .receive (.group "bls12-381.g1") "label_66697273745f636f6d6d69746d656e74_0" 0 <|
  .receive (.group "bls12-381.g1") "label_7365636f6e645f636f6d6d69746d656e74_0" 0 <|
  .query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) .nil) <|
  .send (.field "bls12-381.fr") "label_726573706f6e7365_0" 0 (.var .here) <|
  .receive (.field "bls12-381.fr") "label_726573706f6e7365_0" 0 <|
  .done (.cons (.present (.calc .booleanAnd rfl (.cons (.calc (.groupEqual "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var .here) .nil)) .here) (.cons (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.var (.there (.there (.there .here)))) (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.var (.there .here)) .nil)) .here) .nil)) .here) .nil)) .here) (.cons (.calc (.groupEqual "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.var .here) .nil)) .here) (.cons (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.var (.there (.there .here))) (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.var (.there .here)) .nil)) .here) .nil)) .here) .nil)) .here) .nil)) .here)) .nil)

/-- A literal that is not the normalizer's result is refused by the kernel. -/
example : True := by
  fail_if_success
    have : normalize {} ChaumPedersenBodies.interactiveBody 1 2 ChaumPedersenNormalForms.verifierPattern =
        .ok misdirected := by
      kernel_rfl
  trivial

/-- The checker refuses the same misstated form. -/
example : check {} 1 2 ChaumPedersenBodies.interactiveBody ChaumPedersenNormalForms.verifierPattern
    misdirected = false := by kernel_rfl

/-- The checker accepts the generated form. -/
example : check {} 1 2 ChaumPedersenBodies.interactiveBody ChaumPedersenNormalForms.verifierPattern
    ChaumPedersenNormalForms.verifierForm = true := by kernel_rfl

/-- A role index outside the declared roster is refused: `RosterDistinct`
says nothing about it. -/
example : normalize {} ChaumPedersenBodies.interactiveBody 1 1 ChaumPedersenNormalForms.verifierPattern =
    .error "role-outside-roster" := by kernel_rfl

/-- The Sumcheck round's owned calls need laws: without them the normalizer
refuses rather than unfolding the helper. -/
example : normalize {} SumcheckVerifierBodies.roundBody 0 2 SumcheckRoundNormalForms.proverPattern =
    .error "no-law" := by kernel_rfl

/-- A law pinned to an input the call does not read is refused. -/
example : normalize ⟨[⟨SumcheckHelperBodies.sumsHelper, .returns, [some 2, some 2, some 3]⟩,
      ⟨MapFirstBodies.firstHelper, .returns, []⟩, ⟨SumcheckHelperBodies.appendHelper, .returns, []⟩], false⟩
    SumcheckVerifierBodies.roundBody 0 2 SumcheckRoundNormalForms.proverPattern = .error "law-pins" := by
  kernel_rfl

/-- The Reduce body starts with a Math call, which may stop or depend on the
helper body: it is refused, not presented as a total term. -/
example : normalize {} (SumcheckVerifierBodies.reduceBody 4) 1 2
    (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional .nil)))))) =
    .error "calculation-can-stop" := by kernel_rfl

end Tests.StructuredNormalForms
