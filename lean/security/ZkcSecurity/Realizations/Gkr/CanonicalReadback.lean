module

public import ZkcSecurity.Realizations.Gkr.CanonicalVerifier
public import ZkcSecurity.Source.PairRouting

@[expose] public section

/-! Pairing of the actual occurrence source, before construction. The producer
computes every message; the validator has the same arbitrary challenge prefix.
Coverage and physical return/history installation are shared root theorems. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalReadback
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open ZkcSecurity.Source HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev ValuesResult := Values (Component (assignment F G)) [.boolean]

def Post (left right : ValuesResult (F := F) (G := G)) : Prop :=
  left = .cons none .nil ∧ right = .cons (some true) .nil

theorem actual (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (correct : encoding.Outputs outputs)
    (handle : Nat) (service : Option Nat) (scope : PairScope)
    (roles : scope.producer = 0 ∧ scope.validator = 1)
    (outputDelivery : (GkrVerifier.outputSite {}, GkrVerifier.outputDeliverySite {}) ∈ scope.deliveries)
    (leftDelivery : (GkrVerifier.challengeSite (GkrVerifier.leftContext {}),
      GkrVerifier.deliverySite (GkrVerifier.leftContext {})) ∈ scope.deliveries)
    (rightDelivery : (GkrVerifier.challengeSite (GkrVerifier.rightContext {}),
      GkrVerifier.deliverySite (GkrVerifier.rightContext {})) ∈ scope.deliveries)
    (lineDelivery : (GkrVerifier.lineChallengeSite {}, GkrVerifier.lineDeliverySite {}) ∈ scope.deliveries) :
    Pair scope Post
      (Occurrence.participant (ringModel F G) GkrSourceViews.program 0 (currentInputs encoding outputs service))
      (Occurrence.participant (ringModel F G) GkrSourceViews.program 1 (currentInputs encoding outputs (some handle))) := by
  rw [HonestProducerSource.observed encoding outputs admitted service,
    CanonicalVerifier.reads encoding outputs admitted handle]
  have paired := HonestProducerObserved.pair (G := G) {} scope ⟨roles.1.symm, roles.2.symm⟩
    handle currentSites encoding outputs correct outputDelivery leftDelivery rightDelivery lineDelivery
  simpa only [PIR.Process.bind_done] using paired.bind (Final := Post) PIR.Process.done
    (fun accepted => .done (.cons accepted .nil : ValuesResult (F := F) (G := G))) (by
      rintro p v ⟨rfl, rfl⟩
      exact .done ⟨rfl, rfl⟩)

#print axioms actual
end ZkcSecurity.Realizations.Gkr.CanonicalReadback
