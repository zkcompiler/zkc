module

public import ZkcSecurity.FiatShamir.OccurrenceReading
public import ZkcExamples.Construction.ComposedSumcheckSourceRouting

@[expose] public section

/-! A second source client of the shared nominal reading laws. Both actual
Sumcheck applications retain their source routes and arbitrary raw inputs. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.OccurrenceReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir
variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

theorem sumcheck_reading (left right : List F) (leftClaim rightClaim : F)
    (count handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    let routing := ZkcExamples.Construction.ComposedSumcheckSourceRouting.Retained.routing handle
    let source := Occurrence.participant (ringModel F G)
      ZkcExamples.Construction.ComposedSumcheckSourceRouting.Retained.program 1
      (.cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
        (.cons (some count) (.cons (some handle) .nil))))))
    let routed := ZkcExamples.Construction.ComposedSumcheckSourceRouting.participant (G := G)
      left right leftClaim rightClaim count handle
    DomainReduction.Bridge OccurrenceReading.interface (OccurrenceReading.Post []) history
      (Original.fold routing source ⟨[], history⟩)
      (OccurrenceReading.presentation routed history) :=
  OccurrenceReading.reading rfl _ rfl
    (ZkcExamples.Construction.ComposedSumcheckSourceRouting.participant
      left right leftClaim rightClaim count handle) history

#print axioms sumcheck_reading
#print axioms OccurrenceReading.reading
#print axioms OccurrenceReading.charged
#print axioms OccurrenceReading.cost

end TestsSecurity.OccurrenceReading
