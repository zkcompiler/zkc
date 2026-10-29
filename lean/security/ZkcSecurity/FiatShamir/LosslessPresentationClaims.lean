module

public import ZkcSecurity.FiatShamir.LosslessPresentation
public import ZkcSecurity.FiatShamir.OriginalClaims

@[expose] public section

/-! Install a losslessly reconstructed full-result presentation into the
unchanged compiled charged export. Probability, prices, budgets and exceptional
sets remain owned by the existing derivation and charged reduction engines.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.FiatShamir.Original.Claims.Installation
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.Obligations

variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
variable {subject : ZkcSecurity.Claims.Domain.Subject model art}
variable (installation : Claims.Installation subject)
variable (lossless : ∀ statement initial, LosslessOn installation.absorb (installation.presented statement initial))

/-- Select the proved full-result presentation independently at every statement
and initial history. This logical choice does not encode source return values. -/
def losslessPresentedOn (statement : art.Statement model) (initial : Domain.History model.toCarriers) :
    PIR.Process installation.signature (Domain.Result model.toCarriers) :=
  Classical.choose ((installation.bridge statement initial).exists_lossless_presentation_on (lossless statement initial))

theorem losslessAlignmentOn (statement : art.Statement model) (initial : Domain.History model.toCarriers) :
    Alignment installation.returns (installation.presented statement initial)
      (installation.losslessPresentedOn lossless statement initial) :=
  (Classical.choose_spec ((installation.bridge statement initial).exists_lossless_presentation_on (lossless statement initial))).1

/-- The full source Post and full return relation remain available to callers;
only the final ordinary export below forgets them to its required trivial Post. -/
theorem losslessBridgeOn (statement : art.Statement model) (initial : Domain.History model.toCarriers) :
    DomainReduction.Bridge installation.absorb
      (fun reached b => ∃ a, installation.Post reached a ∧ installation.returns a b) initial
      (Domain.participant model subject.compiled.imported.program subject.compiled.selection.context
        art.participant (Domain.inputFrame subject.compiled.selection.context
          (installation.inputs statement) initial))
      (installation.losslessPresentedOn lossless statement initial) :=
  (Classical.choose_spec ((installation.bridge statement initial).exists_lossless_presentation_on (lossless statement initial))).2

section Charged
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- Produce the existing ordinary charged export from the source installation.
Rejection derivations and pathwise costs transfer along the same all-reply
alignment; no target reading, return encoder or new probability law is a premise.
-/
def losslessChargedExportOn (schedule : ZkcSecurity.Claims.Domain.ChargeSchedule subject)
    (queries : Nat) (validatorCost : ENNReal)
    (rejects : ∀ statement, subject.FalseStatement statement → ∀ initial,
      Zkc.Obligations.Derivation installation.absorb (boundedEscape (schedule.charge queries))
        (fun _ result => installation.acceptance result ≠ some true) initial
        (installation.presented statement initial))
    (costs : ∀ statement initial,
      Typed.ChargedCostBound installation.absorb (schedule.charge queries)
        (installation.presented statement initial) initial validatorCost) :
    ZkcSecurity.Claims.Domain.ChargedExport subject schedule queries validatorCost where
  signature := installation.signature
  absorb := installation.absorb
  inputs := installation.inputs
  encoded := installation.encoded
  presented := installation.losslessPresentedOn lossless
  bridge statement initial :=
    (installation.losslessBridgeOn lossless statement initial).weaken (fun _ _ _ => trivial)
  certificate := (reduction installation.absorb
    (fun _ result => subject.compiled.acceptance result ≠ some true)
    (schedule.charge queries)).toCertificate _ (fun _ _ post => post)
  doomed := by
    intro statement falseStatement initial
    apply derived_doomed
    exact Classical.choice ((installation.losslessAlignmentOn lossless statement initial).derivation
      (rejects statement falseStatement initial) (fun reached a b related rejected => by
        rw [← installation.agrees a b related]
        exact rejected))
  costBound statement initial :=
    (installation.losslessAlignmentOn lossless statement initial).cost (costs statement initial)

end Charged

/-- Installed global laws specialize the same operation-local adapter. -/
abbrev losslessPresented (installation : Claims.Installation subject)
    (lossless : LosslessInterface installation.absorb) :=
  installation.losslessPresentedOn (fun statement initial => lossless.on (installation.presented statement initial))

theorem losslessAlignment (installation : Claims.Installation subject)
    (lossless : LosslessInterface installation.absorb) (statement : art.Statement model)
    (initial : Domain.History model.toCarriers) :
    Alignment installation.returns (installation.presented statement initial)
      (installation.losslessPresented lossless statement initial) :=
  installation.losslessAlignmentOn (fun statement initial => lossless.on (installation.presented statement initial))
    statement initial

theorem losslessBridge (installation : Claims.Installation subject)
    (lossless : LosslessInterface installation.absorb) (statement : art.Statement model)
    (initial : Domain.History model.toCarriers) :
    DomainReduction.Bridge installation.absorb
      (fun reached b => ∃ a, installation.Post reached a ∧ installation.returns a b) initial
      (Domain.participant model subject.compiled.imported.program subject.compiled.selection.context
        art.participant (Domain.inputFrame subject.compiled.selection.context
          (installation.inputs statement) initial))
      (installation.losslessPresented lossless statement initial) :=
  installation.losslessBridgeOn (fun statement initial => lossless.on (installation.presented statement initial))
    statement initial

variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

abbrev losslessChargedExport (installation : Claims.Installation subject)
    (lossless : LosslessInterface installation.absorb) :=
  installation.losslessChargedExportOn
    (fun statement initial => lossless.on (installation.presented statement initial))

end ZkcSecurity.FiatShamir.Original.Claims.Installation
