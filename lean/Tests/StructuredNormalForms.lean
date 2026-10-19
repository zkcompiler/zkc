import Zkc.Source.Structured.NormalForm.Presentation
import ZkcExamples.Structured.ChaumPedersenViews
import ZkcExamples.Structured.SumcheckRoundNormalForms

/-! Controls for the normalizer. The migrated generated modules are the
positive controls; these cases show that the kernel refuses a form literal
that is not the normalizer's result, that the normalizer refuses what is
outside its fragment by name, and that a law use is checked against the law's
own helper. -/
set_option autoImplicit false
namespace Tests.StructuredNormalForms
open Zkc.Source Zkc.Source.Structured NormalForm ZkcExamples.Structured

/-- The Chaum–Pedersen verifier's inputs: the public statement and its challenges. -/
def verifierPattern : InputPattern ChaumPedersenViews.program.payload.entry.inputs :=
  .cons .present (.cons .present (.cons .present (.cons .present (.cons .absent (.cons .absent (.cons .present .nil))))))

/-- The verifier's form with the challenge sent to the response's site. -/
noncomputable def misdirected : Form [] verifierPattern.scope
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
    have : normalize {} ChaumPedersenBodies.interactiveBody 1 2 verifierPattern =
        .ok misdirected := by
      kernel_rfl
  trivial

/-- A role index outside the declared roster is refused: `RosterDistinct`
says nothing about it. -/
example : normalize {} ChaumPedersenBodies.interactiveBody 1 1 verifierPattern =
    .error "role-outside-roster" := by kernel_rfl

/-- The Sumcheck round's owned calls need laws: without them the normalizer
refuses rather than unfolding the helper. -/
example : normalize {} SumcheckVerifierBodies.roundBody 0 2 SumcheckRoundNormalForms.proverPattern =
    .error "no-law" := by kernel_rfl

/-- A law pinned to an input the call does not read is refused. -/
example : normalize ⟨[⟨SumcheckHelperBodies.sumsHelper, .returns, [some 2, some 2, some 3]⟩,
      ⟨MapFirstBodies.firstHelper, .returns, []⟩, ⟨SumcheckHelperBodies.appendHelper, .returns, []⟩], false, false⟩
    SumcheckVerifierBodies.roundBody 0 2 SumcheckRoundNormalForms.proverPattern = .error "law-pins" := by
  kernel_rfl

/-- A helper with the Sumcheck sums helper's kind, inputs and outputs but another name. -/
def renamedSums : Helper := { SumcheckHelperBodies.sumsHelper with name := "renamed" }

/-- A signature whose only law is about the renamed helper. -/
def renamedSignature (names : Bool) : Signature := ⟨[⟨renamedSums, .stops .reject, []⟩], false, names⟩

/-- Choosing laws by signature presents the sums call by the renamed helper's law;
the form records the helper actually called. -/
noncomputable def renamedForm : Form (renamedSignature false).laws
    SumcheckRoundNormalForms.proverEmptyPattern.scope SumcheckVerifierBodies.repeatState :=
  .byLaw ⟨0, by decide⟩ SumcheckHelperBodies.sumsHelper (.halt .reject)

example : normalize (renamedSignature false) SumcheckVerifierBodies.roundBody 0 1
    SumcheckRoundNormalForms.proverEmptyPattern = .ok renamedForm := by kernel_rfl

/-- The law-use check refuses that form: the called helper is not the law's. -/
example : True := by
  fail_if_success
    have : renamedForm.CallsMatch := by kernel_rfl
  trivial

/-- Choosing laws by name finds no law for the call. -/
example : normalize (renamedSignature true) SumcheckVerifierBodies.roundBody 0 1
    SumcheckRoundNormalForms.proverEmptyPattern = .error "no-law" := by kernel_rfl

/-- The Reduce body starts with a Math call, which may stop or depend on the
helper body: it is refused, not presented as a total term. -/
example : normalize {} (SumcheckVerifierBodies.reduceBody 4) 1 2
    (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional .nil)))))) =
    .error "calculation-can-stop" := by kernel_rfl

end Tests.StructuredNormalForms
