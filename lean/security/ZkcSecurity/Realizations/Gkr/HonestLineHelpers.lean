module

public import ZkcSecurity.Realizations.Gkr.HonestHelpersReadback
public import Zkc.Polynomial.Multilinear.LineCoefficients

@[expose] public section

/-! Structural equations for the actual line producer's closed helpers.
Associations check literal bodies in the current admitted export. -/

namespace ZkcSecurity.Realizations.Gkr.HonestLine
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial.Multilinear CoefficientRows LineCoefficients

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper48 := GkrSourceBodies.helper48, helper49 := GkrSourceBodies.helper49,
    helper50 := GkrSourceBodies.helper50, scopedHelper80 := GkrSourceBodies.scopedHelper80,
    helper52 := GkrSourceBodies.helper52, helper58 := GkrSourceBodies.helper58,
    scopedHelper67 := GkrSourceBodies.scopedHelper67, helper60 := GkrSourceBodies.helper60,
    scopedHelper70 := GkrSourceBodies.scopedHelper70, helper62 := GkrSourceBodies.helper62,
    helper63 := GkrSourceBodies.helper63, scopedHelper86 := GkrSourceBodies.scopedHelper86,
    helper65 := GkrSourceBodies.helper65, helper66 := GkrSourceBodies.helper66,
    helper67 := GkrSourceBodies.helper67, scopedHelper73 := GkrSourceBodies.scopedHelper73,
    helper69 := GkrSourceBodies.helper69]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem constant_row_body (table : Meanings F G) (xs : List F) (value : F) (width : Nat) :
    GkrSourceBodies.helper48Body.denote (meaning F G table)
      (Values.cons xs (.cons value (.cons width .nil))).get =
      (invoke table GkrSourceBodies.scopedHelper74Helper .nil).bind fun zero =>
      (invoke table GkrSourceBodies.helper20Helper
        (.cons (xs ++ [value]) (.cons (zero.get .here) (.cons width .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem constant_wrapper_body (table : Meanings F G) (xs : List F) (value : F) (width : Nat) :
    GkrSourceBodies.helper49Body.denote (meaning F G table)
      (Values.cons xs (.cons value (.cons width .nil))).get =
      (invoke table GkrSourceBodies.helper48Helper
        (.cons xs (.cons value (.cons width .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem constant_row (xs : List F) (value : F) (width : Nat) (small : width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper49Helper
      (.cons xs (.cons value (.cons width .nil))) =
        .done (.cons (xs ++ (value :: List.replicate width 0)) .nil) := by
  rw [helper49_association.invoke unit.linked, constant_wrapper_body,
    helper48_association.invoke unit.linked, constant_row_body,
    HonestHelpers.zero_equation]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestHelpers.helper20_association.invoke unit.linked, HonestHelpers.repeat_body _ _ _ _ small]
  simp [PIR.Process.bind, Values.get, List.append_assoc]

abbrev constantFold : FoldSpec :=
  (fold? GkrSourceBodies.scopedHelper80Body).get (by decide +kernel)

theorem constant_step_body (table : Meanings F G) (xs : List F) (value : F)
    (source : List F) (width : Nat) :
    GkrSourceBodies.helper50Body.denote (meaning F G table)
      (Values.cons xs (.cons value (.cons source (.cons width .nil)))).get =
      (invoke table GkrSourceBodies.helper49Helper
        (.cons xs (.cons value (.cons width .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem constant_step (xs : List F) (value : F) (source : List F) (width : Nat)
    (small : width < indexLimit) :
    invoke (helpers (G := G)) constantFold.stepHelper
      (.cons xs (.cons value (.cons source (.cons width .nil)))) =
        .done (.cons (xs ++ (value :: List.replicate width 0)) .nil) := by
  change invoke (helpers (G := G)) GkrSourceBodies.helper50Helper _ = _
  rw [helper50_association.invoke unit.linked, constant_step_body,
    constant_row xs value width small]
  rfl

private def constantTransition (width : Nat)
    (state : Values (assignment F G) constantFold.state) (value : F) :
    Values (assignment F G) constantFold.state :=
  .cons (state.get .here ++ (value :: List.replicate width 0)) .nil

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem constantTransition_fold (values xs : List F) (width : Nat) :
    values.foldl (constantTransition (G := G) width) (.cons xs .nil) =
      .cons (xs ++ values.flatMap (fun v => v :: List.replicate width 0)) .nil := by
  induction values generalizing xs with
  | nil => simp
  | cons v vs ih =>
    simpa [constantTransition, Values.get, List.append_assoc] using
      ih (xs ++ (v :: List.replicate width 0))

theorem constant_fold_body (table : Meanings F G) (values xs : List F) (width : Nat) :
    GkrSourceBodies.scopedHelper80Body.denote (meaning F G table)
      (Values.cons values (.cons xs (.cons width .nil))).get =
      (Evaluation.denoteFold table constantFold
        ((Values.cons values .nil).append ((Values.cons xs .nil).append (.cons width .nil)))).bind
        fun result => .done (.cons (result.get .here) .nil) := by
  derive_process

theorem constant_fold (values xs : List F) (width : Nat)
    (valuesBound : values.length < indexLimit) (small : width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper80Helper
      (.cons values (.cons xs (.cons width .nil))) =
        .done (.cons (xs ++ values.flatMap (fun v => v :: List.replicate width 0)) .nil) := by
  rw [scopedHelper80_association.invoke unit.linked, constant_fold_body]
  rw [Evaluation.denoteFold_reference_map (helpers (F := F) (G := G)) constantFold
    (.cons values .nil) (.cons xs .nil) (.cons width .nil) values
    (fun value => .cons value .nil)
    (Evaluation.elements_admit _ _ _ _ _ valuesBound)
    (constantTransition width) (fun _ => True) trivial (by
      intro state value _ _
      rw [Evaluation.foldTransition_unfiltered _ _ rfl]
      rcases state with _ | ⟨current, _ | _⟩
      exact ⟨constant_step (F := F) (G := G) current value values width small, trivial⟩)]
  rw [constantTransition_fold (F := F) (G := G) values xs width]
  rfl

theorem constant_rows_body (table : Meanings F G) (values xs : List F) (width : Nat) :
    GkrSourceBodies.helper52Body.denote (meaning F G table)
      (Values.cons xs (.cons width (.cons values .nil))).get =
      (invoke table GkrSourceBodies.scopedHelper80Helper
        (.cons values (.cons xs (.cons width .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem constant_rows (values xs : List F) (width : Nat)
    (valuesBound : values.length < indexLimit) (small : width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper52Helper
      (.cons xs (.cons width (.cons values .nil))) =
        .done (.cons (xs ++ values.flatMap (fun v => v :: List.replicate width 0)) .nil) := by
  rw [helper52_association.invoke unit.linked, constant_rows_body,
    constant_fold values xs width valuesBound small]
  rfl

theorem difference_body (table : Meanings F G) (high low : F) :
    GkrSourceBodies.scopedHelper67Body.denote (meaning F G table)
      (Values.cons high (.cons low .nil)).get =
      (invoke table GkrSourceBodies.helper58Helper (.cons high (.cons low .nil))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem difference (high low : F) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper67Helper (.cons high (.cons low .nil)) =
      .done (.cons (high - low) .nil) := by
  rw [scopedHelper67_association.invoke unit.linked, difference_body,
    helper58_association.invoke unit.linked]
  rfl

theorem slope (low high delta : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper60Helper
      (.cons low (.cons high (.cons delta .nil))) =
        .done (.cons ((high - low) * delta) .nil) := by
  rw [helper60_association.invoke unit.linked]
  rfl

abbrev slopeCollection : CollectSpec :=
  (collection? GkrSourceBodies.scopedHelper70Body).get (by decide +kernel)

abbrev totalCollection : CollectSpec :=
  (collection? GkrSourceBodies.scopedHelper73Body).get (by decide +kernel)

/-- These bindings are read from the typed collection, including its captures. -/
abbrev slopeBindings : MultilinearCollectBodies.Bindings :=
  ⟨GkrSourceBodies.scopedHelper70Helper.name, slopeCollection.domain.name,
    slopeCollection.body, GkrSourceBodies.scopedHelper68Helper.name⟩

abbrev totalBindings : MultilinearCollectBodies.Bindings :=
  ⟨GkrSourceBodies.scopedHelper73Helper.name, totalCollection.domain.name,
    totalCollection.body, GkrSourceBodies.scopedHelper71Helper.name⟩

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [scopedHelper68 := GkrSourceBodies.scopedHelper68,
    scopedHelper69 := GkrSourceBodies.scopedHelper69,
    scopedHelper71 := GkrSourceBodies.scopedHelper71,
    scopedHelper72 := GkrSourceBodies.scopedHelper72,
    scopedHelper66 := GkrSourceBodies.scopedHelper66]

theorem slope_callback (left right : List F) (lo hi delta : F) :
    invoke (helpers (G := G)) slopeCollection.bodyHelper
      (.cons lo (.cons hi (.cons left (.cons right (.cons delta .nil))))) =
      .done (.cons (((hi - lo) * delta : F)) .nil) := by
  change invoke (helpers (G := G)) GkrSourceBodies.scopedHelper69Helper
    (.cons lo (.cons hi (.cons left (.cons right (.cons delta .nil))))) = _
  rw [scopedHelper69_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.scopedHelper68Helper
    (.cons lo (.cons hi (.cons delta .nil)))).bind _ = _
  rw [scopedHelper68_association.invoke unit.linked]
  change ((invoke (helpers (G := G)) GkrSourceBodies.helper60Helper
    (.cons lo (.cons hi (.cons delta .nil)))).bind _).bind _ = _
  rw [slope]
  rfl

theorem slope_map_body (table : Meanings F G) (left right : List F) (delta : F) :
    GkrSourceBodies.scopedHelper70Body.denote (meaning F G table)
      (Values.cons left (.cons right (.cons delta .nil))).get =
      (Evaluation.denoteCollect table slopeCollection
        (.cons left (.cons right (.cons delta .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem slope_map (left right : List F) (delta : F)
    (small : left.length < indexLimit) (same : right.length = left.length) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper70Helper
      (.cons left (.cons right (.cons delta .nil))) =
        .done (.cons (List.zipWith (fun a b => (b - a) * delta) left right) .nil) := by
  rw [scopedHelper70_association.invoke unit.linked, slope_map_body]
  have collected := Evaluation.denoteCollect_reference (helpers (F := F) (G := G)) slopeCollection
    (.cons left (.cons right .nil)) (.cons delta .nil) (left.zip right)
    (fun pair => .cons pair.1 (.cons pair.2 .nil))
    (MultilinearCollectLaws.domain_admit slopeBindings left right small same.symm) rfl
    (fun pair => (pair.2 - pair.1) * delta) (by
      intro pair _; exact slope_callback left right pair.1 pair.2 delta)
  simp only [Values.append] at collected
  rw [collected]
  simp only [PIR.Process.bind, Values.get, Collection.pack, List.map_zip_eq_zipWith]
  rfl

theorem total (left right : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper67Helper (.cons left (.cons right .nil)) =
      .done (.cons (left + right) .nil) := by
  rw [helper67_association.invoke unit.linked]
  rfl

theorem total_callback (left right : List F) (lo hi : F) :
    invoke (helpers (G := G)) totalCollection.bodyHelper
      (.cons lo (.cons hi (.cons left (.cons right .nil)))) =
      .done (.cons ((lo + hi : F)) .nil) := by
  change invoke (helpers (G := G)) GkrSourceBodies.scopedHelper72Helper
    (.cons lo (.cons hi (.cons left (.cons right .nil)))) = _
  rw [scopedHelper72_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.scopedHelper71Helper
    (.cons lo (.cons hi .nil))).bind _ = _
  rw [scopedHelper71_association.invoke unit.linked]
  change ((invoke (helpers (G := G)) GkrSourceBodies.helper67Helper
    (.cons lo (.cons hi .nil))).bind _).bind _ = _
  rw [total]
  rfl

theorem total_map_body (table : Meanings F G) (left right : List F) :
    GkrSourceBodies.scopedHelper73Body.denote (meaning F G table)
      (Values.cons left (.cons right .nil)).get =
      (Evaluation.denoteCollect table totalCollection
        (.cons left (.cons right .nil))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem total_map (left right : List F)
    (small : left.length < indexLimit) (same : right.length = left.length) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper73Helper (.cons left (.cons right .nil)) =
      .done (.cons (List.zipWith (· + ·) left right) .nil) := by
  rw [scopedHelper73_association.invoke unit.linked, total_map_body]
  have collected := Evaluation.denoteCollect_reference (helpers (F := F) (G := G)) totalCollection
    (.cons left (.cons right .nil)) .nil (left.zip right)
    (fun pair => .cons pair.1 (.cons pair.2 .nil))
    (MultilinearCollectLaws.domain_admit totalBindings left right small same.symm) rfl
    (fun pair => pair.1 + pair.2) (by
      intro pair _; exact total_callback left right pair.1 pair.2)
  simp only [Values.append] at collected
  rw [collected]
  simp only [PIR.Process.bind, Values.get, Collection.pack, List.map_zip_eq_zipWith]
  rfl

/-- The line contraction uses a separate admission of the same checked body. -/
theorem base_map (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper66Helper
      (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) := by
  rw [scopedHelper66_association.invoke unit.linked]
  change (MultilinearCollectBodies.mapBody
    { lineBindings with collection := GkrSourceBodies.scopedHelper66Helper.name }).denote
    (meaning F G helpers) (Values.cons start (.cons finish (.cons t .nil))).get = _
  exact MultilinearCollectLaws.map_body helpers _ start finish t small sameLength.symm
    (fun lo hi => line_callback_equation start finish lo hi t)

end ZkcSecurity.Realizations.Gkr.HonestLine
