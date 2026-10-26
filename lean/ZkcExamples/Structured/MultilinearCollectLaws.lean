module

public import ZkcExamples.Structured.MultilinearCollectBodies
public import Zkc.Source.Structured.Meaning
public import Zkc.Source.Structured.CollectLaws
public import Zkc.Source.DeriveRegion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Equations for the exact ordered collection used by multilinear restriction.
Bindings remain explicit; callback equations retain both rows and the broadcast
argument, even when the scalar computation does not inspect the complete rows. -/
namespace ZkcExamples.Structured.MultilinearCollectLaws
open Zkc.Source Zkc.Source.Structured MultilinearCollectBodies
set_option smartUnfolding true

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem domain_admit (bindings : Bindings) (low high : List F)
    (small : low.length < indexLimit) (sameLength : low.length = high.length) :
    (collectSpec bindings).domain.admit (carriers := uniformCarriers F G)
      (.cons low (.cons high .nil)) =
      .returned ((low.zip high).map fun pair => .cons pair.1 (.cons pair.2 .nil)) := by
  have highSmall : high.length < indexLimit := sameLength ▸ small
  change Finite.continueWith
    (if low.length < indexLimit then
      .returned (low.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
    else .stopped .exhausted) (fun lows =>
      Finite.continueWith
        (if high.length < indexLimit then
          .returned (high.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
        else .stopped .exhausted) (fun highs =>
          Finite.continueWith (zipDomainRows (.cons lows (.cons highs .nil)))
            (fun rows => .returned rows))) = _
  simp only [highSmall, ↓reduceIte, Finite.continueWith, zipDomainRows,
    List.map_map, Values.append, List.length_map, sameLength, List.zip_map,
    Function.comp_def, Prod.map_fst, Prod.map_snd]


theorem callback_body (table : Meanings F G) (bindings : Bindings)
    (lo hi r : F) (low high : List F) :
    (mapCallbackBody bindings).denote (meaning F G table)
      (Values.cons lo (.cons hi (.cons low (.cons high (.cons r .nil))))).get =
      (invoke table (interpolateRealizationHelper bindings)
        (.cons lo (.cons hi (.cons r .nil)))).bind fun result =>
          .done (.cons (result.get .here) .nil) := by
  derive_process

theorem realization_body (table : Meanings F G) (bindings : Bindings)
    (lo hi r : F) :
    (interpolateRealizationBody bindings).denote (meaning F G table)
      (Values.cons lo (.cons hi (.cons r .nil))).get =
      (invoke table interpolateHelper (.cons lo (.cons hi (.cons r .nil)))).bind fun result =>
        .done (.cons (result.get .here) .nil) := by
  derive_process

theorem map_body (table : Meanings F G) (bindings : Bindings)
    (low high : List F) (r : F) (small : low.length < indexLimit)
    (sameLength : low.length = high.length)
    (callback : ∀ lo hi,
      invoke table (mapCallbackHelper bindings)
        (.cons lo (.cons hi (.cons low (.cons high (.cons r .nil))))) =
        .done (.cons (lo + (hi - lo) * r) .nil)) :
    (mapBody bindings).denote (meaning F G table)
      (Values.cons low (.cons high (.cons r .nil))).get =
      .done (.cons (List.zipWith (fun lo hi => lo + (hi - lo) * r) low high) .nil) := by
  have collected := Evaluation.denoteCollect_reference table (collectSpec bindings)
    (.cons low (.cons high .nil)) (.cons r .nil) (low.zip high)
    (fun pair => .cons pair.1 (.cons pair.2 .nil))
    (domain_admit bindings low high small sameLength) rfl
    (fun pair => pair.1 + (pair.2 - pair.1) * r)
    (fun pair _ => callback pair.1 pair.2)
  have expanded : (mapBody bindings).denote (meaning F G table)
      (Values.cons low (.cons high (.cons r .nil))).get =
      (Evaluation.denoteCollect table (collectSpec bindings)
        (.cons low (.cons high (.cons r .nil)))).bind fun result =>
          .done (.cons (result.get .here) .nil) := by
    derive_process
  change Evaluation.denoteCollect table (collectSpec bindings)
    (.cons low (.cons high (.cons r .nil))) =
      .done (.cons ((low.zip high).map fun pair => pair.1 + (pair.2 - pair.1) * r) .nil)
    at collected
  rw [expanded, collected]
  simp only [PIR.Process.bind, Values.get, List.map_zip_eq_zipWith]
  rfl

end ZkcExamples.Structured.MultilinearCollectLaws
