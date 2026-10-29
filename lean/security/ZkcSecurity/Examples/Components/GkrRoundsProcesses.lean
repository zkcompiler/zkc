module

public import ZkcSecurity.Examples.Components.GkrRoundsHelpers
public import ZkcExamples.Structured.SumcheckHelperExpansions
public import ZkcExamples.Structured.MultilinearCollectLaws
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! Full operational equations for `round_message` and `fix_gates`. The raw
views retain ordered split checks, map capacity/shape checks and all stops. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsProcesses
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.GkrSourceViews
open GkrRoundsHelpers
open ZkcExamples.Structured.SumcheckHelperLaws (prepend_empty prepend_one prepend_two prepend_three singleton_eta)
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev vector := Ty.vector "bls12-381.fr"
abbrev scalar := Ty.field "bls12-381.fr"

def split (xs : List F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector, vector]) :=
  primitiveOutcome (Primitive.evaluate (.vectorSplit "bls12-381.fr") (.cons xs .nil))

def round (a m l r : List F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [scalar, scalar, scalar]) :=
  (split a).bind fun a => (split m).bind fun m =>
  (split l).bind fun l => (split r).bind fun r =>
  (mapped (G := G) (Evaluation.mapShape [(a.get .here).length, (m.get .here).length,
      (l.get .here).length, (r.get .here).length])
    (valuesFormula (a.get .here) (m.get .here) (l.get .here) (r.get .here))).bind fun low =>
  (mapped (G := G) (Evaluation.mapShape [(a.get (.there .here)).length, (m.get (.there .here)).length,
      (l.get (.there .here)).length, (r.get (.there .here)).length])
    (valuesFormula (a.get (.there .here)) (m.get (.there .here))
      (l.get (.there .here)) (r.get (.there .here)))).bind fun high =>
  (mapped (G := G) (Evaluation.mapShape [(a.get .here).length, (a.get (.there .here)).length,
      (m.get .here).length, (m.get (.there .here)).length,
      (l.get .here).length, (l.get (.there .here)).length,
      (r.get .here).length, (r.get (.there .here)).length])
    (quadraticsFormula (a.get .here) (a.get (.there .here))
      (m.get .here) (m.get (.there .here)) (l.get .here) (l.get (.there .here))
      (r.get .here) (r.get (.there .here)))).bind fun q =>
  .done (.cons (low.get .here).sum
    (.cons ((high.get .here).sum - (low.get .here).sum - (q.get .here).sum)
      (.cons (q.get .here).sum .nil)))

theorem round_equation (a m l r : List F) :
    invoke (table (G := G)) roundMessageHelper (.cons a (.cons m (.cons l (.cons r .nil)))) =
      round a m l r := by
  rw [round_message_body]
  simp only [roundMessageBody, Region.denote, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty,
    prepend_one, prepend_two, Environment.push,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate,
    ← List.sum_eq_foldl, map_values_left, map_values_right, map_quadratics, linear]
  rfl

abbrev interpolationBindings : ZkcExamples.Structured.MultilinearCollectBodies.Bindings where
  collection := interpolationsHelper.name
  domain := interpolationsCollection.domain.name
  callback := interpolationCallbackHelper.name
  computation := interpolationRealizationHelper.name

theorem map_interpolate (low high : List F) (r : F)
    (small : low.length < indexLimit) (same : high.length = low.length) :
    invoke (table (G := G)) interpolationsHelper (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (List.zipWith (fun a b => a + (b - a) * r) low high) .nil) := by
  rw [interpolations_body]
  change (ZkcExamples.Structured.MultilinearCollectBodies.mapBody interpolationBindings).denote
    (Evaluation.meaning (.silent _) table) (Values.cons low (.cons high (.cons r .nil))).get = _
  apply ZkcExamples.Structured.MultilinearCollectLaws.map_body table interpolationBindings low high r small same.symm
  intro lo hi
  change invoke table interpolationCallbackHelper
    (.cons lo (.cons hi (.cons low (.cons high (.cons r .nil))))) = _
  rw [interpolationCallback_body]
  change (invoke table interpolationRealizationHelper (.cons lo (.cons hi (.cons r .nil)))).bind _ = _
  rw [interpolationRealization_body]
  change ((invoke table interpolationHelper (.cons lo (.cons hi (.cons r .nil)))).bind _).bind _ = _
  rw [interpolate]
  rfl

def fix (xs : List F) (r : F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector]) :=
  (split xs).bind fun halves =>
    invoke table interpolationsHelper (.cons (halves.get .here)
      (.cons (halves.get (.there .here)) (.cons r .nil)))

theorem fix_equation (xs : List F) (r : F) :
    invoke (table (G := G)) factorRestrictionHelper (.cons xs (.cons r .nil)) = fix xs r := by
  rw [factor_restriction_body]
  simp only [factorRestrictionBody, Region.denote, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, prepend_empty,
    prepend_one, prepend_two, Environment.push, SiteObservations.silent, PIR.Process.bind]
  unfold fix split
  congr 1
  funext halves
  cases halves with
  | cons low rest => cases rest with
    | cons high rest => cases rest
                        simp only [singleton_eta, PIR.Process.bind_done]

def fixGates (a m l r : List F) (challenge : F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector, vector, vector, vector]) :=
  (fix a challenge).bind fun a => (fix m challenge).bind fun m =>
  (fix l challenge).bind fun l => (fix r challenge).bind fun r =>
  .done (.cons (a.get .here) (.cons (m.get .here) (.cons (l.get .here) (.cons (r.get .here) .nil))))

theorem fixGates_equation (a m l r : List F) (challenge : F) :
    invoke (table (G := G)) gateRestrictionHelper
      (.cons a (.cons m (.cons l (.cons r (.cons challenge .nil))))) =
      fixGates a m l r challenge := by
  rw [gate_restriction_body]
  simp only [gateRestrictionBody, Region.denote, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, prepend_empty,
    prepend_one, Environment.push, SiteObservations.silent, PIR.Process.bind, fix_equation]
  rfl

/-- Source map capacity is checked before scalar interpolation. -/
theorem map_interpolate_exhausted (low high : List F) (r : F)
    (large : ¬ low.length < indexLimit) :
    invoke (table (G := G)) interpolationsHelper (.cons low (.cons high (.cons r .nil))) =
      .halt .exhausted := by
  rw [interpolations_body]
  change (Evaluation.denoteCollect table interpolationsCollection
    (.cons low (.cons high (.cons r .nil)))).bind _ = _
  have stopped : interpolationsCollection.domain.admit (carriers := uniformCarriers F G)
      (.cons low (.cons high .nil)) = .stopped .exhausted := by
    change Finite.continueWith
      (if low.length < indexLimit then
        .returned (low.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
      else .stopped .exhausted) _ = _
    rw [ite_eq_right large]
    rfl
  have halted : Evaluation.denoteCollect (table (F := F) (G := G)) interpolationsCollection
      (.cons low (.cons high (.cons r .nil))) = .halt .exhausted := by
    simpa only [Values.append] using
      Evaluation.denoteCollect_admission_stop table interpolationsCollection
        (.cons low (.cons high .nil)) (.cons r .nil) .exhausted stopped
  rw [halted]
  rfl

/-- Complete raw-input equation: malformed splits refuse; valid halves check
map capacity. No global power-of-two shape is invented by this helper. -/
theorem fix_all (xs : List F) (r : F) :
    fix (G := G) xs r =
      if 0 < xs.length ∧ xs.length % 2 = 0 then
        if xs.length / 2 < indexLimit then .done (.cons (restrictValues xs r) .nil)
        else .halt .exhausted
      else .halt .refused := by
  by_cases shape : 0 < xs.length ∧ xs.length % 2 = 0
  · have even : xs.length = 2 * (xs.length / 2) := by omega
    obtain ⟨low, high⟩ := restrictValues_halves_length xs even
    unfold fix split
    simp only [Primitive.evaluate, shape, and_self, ite_true, primitiveOutcome, PIR.Process.bind]
    change invoke table interpolationsHelper
      (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) (.cons r .nil))) = _
    by_cases capacity : xs.length / 2 < indexLimit
    · rw [ite_eq_left capacity]
      exact map_interpolate _ _ r (by omega) (by omega)
    · rw [ite_eq_right capacity]
      exact map_interpolate_exhausted _ _ r (by omega)
  · simp only [fix, split, Primitive.evaluate, shape, ite_false, primitiveOutcome, PIR.Process.bind]

end
end ZkcSecurity.Examples.Components.GkrRoundsProcesses
