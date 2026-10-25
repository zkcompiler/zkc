module

import ZkcSecurity.FiatShamir.LosslessPresentationClaims

set_option autoImplicit false
namespace TestsSecurity.LosslessPresentation
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Original

variable {carriers : Structured.Carriers} {I : PIR.Signature} {A B : Type}
variable {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
variable {Post : Domain.History carriers → A → Prop} {returns : A → B → Prop}
variable {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
variable {source : PIR.Process (Domain.effects carriers) A}
variable {target : PIR.Process (Domain.effects carriers) B}
variable {presented : PIR.Process I A} {history : Domain.History carriers}

/-- Symbolic unrelated return types, arbitrary full relation and source Post.
Costs and derivations move with the exact same reconstructed witness. -/
example (lossless : LosslessInterface absorb)
    (bridge : Original.Bridge absorb Post history source target presented returns live)
    (charge : Domain.History carriers → Domain.Event carriers → ENNReal) (budget : ENNReal)
    (cost : Typed.ChargedCostBound absorb charge presented history budget)
    (escape : EscapeJudgment (Domain.Event carriers) Domain.Raw)
    (SourcePost : Domain.History carriers → A → Prop)
    (TargetPost : Domain.History carriers → B → Prop)
    (proof : Zkc.Obligations.Derivation absorb escape SourcePost history presented)
    (terminal : ∀ reached a b, returns a b → SourcePost reached a → TargetPost reached b) :
    ∃ targetPresented : PIR.Process I B,
      Alignment returns presented targetPresented ∧
      DomainReduction.Bridge absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented ∧
      Typed.ChargedCostBound absorb charge targetPresented history budget ∧
      Nonempty (Zkc.Obligations.Derivation absorb escape TargetPost history targetPresented) := by
  obtain ⟨after, aligned, reading⟩ := bridge.exists_lossless_presentation lossless
  exact ⟨after, aligned, reading, aligned.cost cost, aligned.derivation proof terminal⟩

noncomputable section Claims
variable {model : Structured.DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
variable {subject : ZkcSecurity.Claims.Domain.Subject model art}
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- The constructed value has precisely the existing ordinary export type. -/
example (installation : Original.Claims.Installation subject)
    (lossless : LosslessInterface installation.absorb)
    (schedule : ZkcSecurity.Claims.Domain.ChargeSchedule subject)
    (queries : Nat) (budget : ENNReal)
    (rejects : ∀ statement, subject.FalseStatement statement → ∀ initial,
      Zkc.Obligations.Derivation installation.absorb
        (ZkcSecurity.Obligations.boundedEscape (schedule.charge queries))
        (fun _ result => installation.acceptance result ≠ some true) initial
        (installation.presented statement initial))
    (costs : ∀ statement initial,
      Typed.ChargedCostBound installation.absorb (schedule.charge queries)
        (installation.presented statement initial) initial budget) :
    ZkcSecurity.Claims.Domain.ChargedExport subject schedule queries budget :=
  installation.losslessChargedExport lossless schedule queries budget rejects costs
end Claims

#print axioms exists_lossless_reading
#print axioms Original.Bridge.exists_lossless_presentation
#print axioms Original.Claims.Installation.losslessPresented
#print axioms Original.Claims.Installation.losslessAlignment
#print axioms Original.Claims.Installation.losslessBridge
#print axioms Original.Claims.Installation.losslessChargedExport

end TestsSecurity.LosslessPresentation
