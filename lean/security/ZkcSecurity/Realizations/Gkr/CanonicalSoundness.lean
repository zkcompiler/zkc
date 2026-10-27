module

public import ZkcSecurity.Realizations.Gkr.CanonicalInstallation
public import ZkcSecurity.Realizations.Gkr.CanonicalSchedule
public import ZkcSecurity.FiatShamir.LosslessPresentationClaims

@[expose] public section

/-! Adaptive soundness of the actual compiled validator at its fixed registered
circuit-output target. Every typed public statement uses the same full nominal
installation, including statements rejected by the source admission guards. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalSoundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity ZkcSecurity.Claims ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open Generated.Subject
open CanonicalInstallation
abbrev Scalar := ZMod blsModulus
local instance : AddCommGroup Scalar := (inferInstance : Field Scalar).toAddCommGroup
local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
local instance : DecidableEq (Domain.Event (uniformCarriers Scalar Scalar)) := Classical.decEq _
local instance rawSampling : ∀ event : Domain.Event (uniformCarriers Scalar Scalar),
    SampleableType (Domain.Raw event) := Domains.PrimeField.rawSampleable blsModulus

/-- The concrete capability and the generic nominal reading use the same
uniform samples at every typed event. -/
theorem sampling :
    (OccurrenceReading.rawSampleable (F := Scalar) (G := Scalar)) =
      Domains.PrimeField.rawSampleable blsModulus := by
  funext event
  cases event with
  | message => rfl
  | publicBinding => rfl
  | challenge origin =>
      rcases origin with ⟨entry, events, request⟩
      cases request with
      | none => rfl
      | some request =>
          rcases request with ⟨method, parameters, sort⟩
          cases sort <;> rfl

def schedule : Claims.Domain.ChargeSchedule validatorSubject := CanonicalSchedule.schedule
def validatorCost : Nat → ENNReal := CanonicalSchedule.validatorCost
def scalarBound : Nat → ENNReal := CanonicalSchedule.scalarBound

theorem scalar_bound (queries : Nat) :
    (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ scalarBound queries :=
  CanonicalSchedule.scalar_bound queries

def reductionExport (queries : Nat) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (validatorCost queries) :=
  installation.losslessChargedExport OccurrenceReading.lossless schedule queries (validatorCost queries)
    (by
      rw [CompiledSoundness.charge_constant schedule queries CanonicalSchedule.price
        (by decide +kernel) (CanonicalSchedule.schedule_prices queries)]
      intro statement wrong history
      have samples : rawSampling = OccurrenceReading.rawSampleable (F := Scalar) (G := Scalar) := sampling.symm
      rw [samples]
      simpa only [installation, CanonicalSchedule.price, CanonicalReading.price, Canonical.invocation] using
        (CanonicalReading.rejected statement 0 wrong history))
    (by
      rw [CompiledSoundness.charge_constant schedule queries CanonicalSchedule.price
        (by decide +kernel) (CanonicalSchedule.schedule_prices queries)]
      intro statement history
      simpa only [installation, CanonicalSchedule.price, CanonicalReading.price, CanonicalSchedule.validatorCost, validatorCost] using
        (CanonicalReading.costs (Canonical.invocation model statement 0) history))

end ZkcSecurity.Realizations.Gkr.CanonicalSoundness
