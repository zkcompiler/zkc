module

public import ZkcSecurity.Bindings.Gkr.RoundsProcesses
public import ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation
public import Zkc.Protocols.Sumcheck.Source.HelperExpansions
public import Zkc.Protocols.Multilinear.Source.CollectLaws
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

set_option autoImplicit false

/-! Full operational equations for `round_message` and `fix_gates`. The raw
views retain ordered split checks, map capacity/shape checks and all stops. -/

namespace ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Examples.Components.GkrRoundsHelpers
open ZkcSecurity.Examples.Components.GkrRoundsProcesses
open RoundsHelperInstallation
open ZkcExamples.Structured.SumcheckHelperLaws (prepend_empty prepend_one prepend_two prepend_three singleton_eta)
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

variable {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (bodies : RoundsHelperInstallation.RestrictionBodies definitions)
include linked bodies

omit bodies in
theorem round_equation (bodies : RoundsHelperInstallation.Bodies definitions) (a m l r : List F) :
    invoke (table (G := G) definitions) roundMessageHelper (.cons a (.cons m (.cons l (.cons r .nil)))) =
      round a m l r := by
  rw [round_message_body linked bodies]
  simp only [roundMessageBody, Region.denote, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty,
    prepend_one, prepend_two, Environment.push,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate,
    ← List.sum_eq_foldl, map_values_left linked bodies, map_values_right linked bodies, map_quadratics linked bodies, linear linked bodies]
  rfl

theorem map_interpolate (low high : List F) (r : F)
    (small : low.length < indexLimit) (same : high.length = low.length) :
    invoke (table (G := G) definitions) interpolationsHelper (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (List.zipWith (fun a b => a + (b - a) * r) low high) .nil) := by
  rw [interpolations_body linked bodies]
  change (ZkcExamples.Structured.MultilinearCollectBodies.mapBody interpolationBindings).denote
    (Evaluation.meaning (.silent _) (table definitions)) (Values.cons low (.cons high (.cons r .nil))).get = _
  apply ZkcExamples.Structured.MultilinearCollectLaws.map_body (table definitions) interpolationBindings low high r small same.symm
  intro lo hi
  change invoke (table definitions) interpolationCallbackHelper
    (.cons lo (.cons hi (.cons low (.cons high (.cons r .nil))))) = _
  rw [interpolationCallback_body linked bodies]
  change (invoke (table definitions) interpolationRealizationHelper (.cons lo (.cons hi (.cons r .nil)))).bind _ = _
  rw [interpolationRealization_body linked bodies]
  change ((invoke (table definitions) interpolationHelper (.cons lo (.cons hi (.cons r .nil)))).bind _).bind _ = _
  rw [interpolate linked bodies]
  rfl

def fix (definitions : List CheckedDefinition) (xs : List F) (r : F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector]) :=
  (split xs).bind fun halves =>
    invoke (table definitions) interpolationsHelper (.cons (halves.get .here)
      (.cons (halves.get (.there .here)) (.cons r .nil)))

theorem fix_equation (xs : List F) (r : F) :
    invoke (table (G := G) definitions) factorRestrictionHelper (.cons xs (.cons r .nil)) = (fix definitions) xs r := by
  rw [factor_restriction_body linked bodies]
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

def fixGates (definitions : List CheckedDefinition) (a m l r : List F) (challenge : F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector, vector, vector, vector]) :=
  ((fix definitions) a challenge).bind fun a => ((fix definitions) m challenge).bind fun m =>
  ((fix definitions) l challenge).bind fun l => ((fix definitions) r challenge).bind fun r =>
  .done (.cons (a.get .here) (.cons (m.get .here) (.cons (l.get .here) (.cons (r.get .here) .nil))))

omit bodies in
theorem fixGates_equation (bodies : RoundsHelperInstallation.Bodies definitions) (a m l r : List F) (challenge : F) :
    invoke (table (G := G) definitions) gateRestrictionHelper
      (.cons a (.cons m (.cons l (.cons r (.cons challenge .nil))))) =
      fixGates definitions a m l r challenge := by
  rw [gate_restriction_body linked bodies]
  simp only [gateRestrictionBody, Region.denote, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, prepend_empty,
    prepend_one, Environment.push, SiteObservations.silent, PIR.Process.bind, fix_equation linked bodies.toRestrictionBodies]
  rfl

/-- Source map capacity is checked before scalar interpolation. -/
theorem map_interpolate_exhausted (low high : List F) (r : F)
    (large : ¬ low.length < indexLimit) :
    invoke (table (G := G) definitions) interpolationsHelper (.cons low (.cons high (.cons r .nil))) =
      .halt .exhausted := by
  rw [interpolations_body linked bodies]
  change (Evaluation.denoteCollect (table definitions) interpolationsCollection
    (.cons low (.cons high (.cons r .nil)))).bind _ = _
  have stopped : interpolationsCollection.domain.admit (carriers := uniformCarriers F G)
      (.cons low (.cons high .nil)) = .stopped .exhausted := by
    change Finite.continueWith
      (if low.length < indexLimit then
        .returned (low.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
      else .stopped .exhausted) _ = _
    rw [ite_eq_right large]
    rfl
  have halted : Evaluation.denoteCollect (table (F := F) (G := G) definitions) interpolationsCollection
      (.cons low (.cons high (.cons r .nil))) = .halt .exhausted := by
    simpa only [Values.append] using
      Evaluation.denoteCollect_admission_stop (table definitions) interpolationsCollection
        (.cons low (.cons high .nil)) (.cons r .nil) .exhausted stopped
  rw [halted]
  rfl

/-- Complete raw-input equation: malformed splits refuse; valid halves check
map capacity. No global power-of-two shape is invented by this helper. -/
theorem fix_all (xs : List F) (r : F) :
    (fix (G := G) definitions) xs r =
      if 0 < xs.length ∧ xs.length % 2 = 0 then
        if xs.length / 2 < indexLimit then .done (.cons (restrictValues xs r) .nil)
        else .halt .exhausted
      else .halt .refused := by
  by_cases shape : 0 < xs.length ∧ xs.length % 2 = 0
  · have even : xs.length = 2 * (xs.length / 2) := by omega
    obtain ⟨low, high⟩ := restrictValues_halves_length xs even
    unfold fix split
    simp only [Primitive.evaluate, shape, and_self, ite_true, primitiveOutcome, PIR.Process.bind]
    change invoke (table definitions) interpolationsHelper
      (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) (.cons r .nil))) = _
    by_cases capacity : xs.length / 2 < indexLimit
    · rw [ite_eq_left capacity]
      exact map_interpolate linked bodies _ _ r (by omega) (by omega)
    · rw [ite_eq_right capacity]
      exact map_interpolate_exhausted linked bodies _ _ r (by omega)
  · simp only [fix, split, Primitive.evaluate, shape, ite_false, primitiveOutcome, PIR.Process.bind]

/-- Complete optional-input behavior of the installed local restriction call.
An inactive owner preserves an absent result without forcing any input. -/
theorem owned_fix (self owner : Nat)
    (args : Values (Component (assignment F G)) factorRestrictionHelper.inputs) :
    Participant.owned self owner (invoke (table (F := F) (G := G) definitions)
      factorRestrictionHelper) args =
      if owner = self then
        match RoleFamily.sequence args with
        | none => .halt .incomplete
        | some values => (fix definitions (values.get .here)
            (values.get (.there .here))).bind fun result => .done result.present
      else .done (Values.absent (assignment F G) factorRestrictionHelper.outputs) := by
  unfold Participant.owned
  split
  · cases sequenced : RoleFamily.sequence args with
    | none => rfl
    | some values =>
      cases values with
      | cons xs rest => cases rest with
        | cons challenge rest => cases rest
                                 dsimp only
                                 rw [fix_equation linked bodies]
                                 rfl
  · rfl

end
end ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation
