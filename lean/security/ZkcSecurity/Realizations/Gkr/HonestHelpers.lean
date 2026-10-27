module

public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcSecurity.Examples.Components.GkrRoundsLayout

@[expose] public section

/-! Laws of the admitted GKR producer's vector helpers. Every invocation uses
its original closed helper table. Index and vector admission bounds are kept
explicit; no equation assumes a helper's correctness. -/

namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial.Multilinear

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper20 := GkrSourceBodies.helper20, helper21 := GkrSourceBodies.helper21,
    helper22 := GkrSourceBodies.helper22, scopedHelper45 := GkrSourceBodies.scopedHelper45,
    helper24 := GkrSourceBodies.helper24, helper25 := GkrSourceBodies.helper25,
    helper26 := GkrSourceBodies.helper26, helper27 := GkrSourceBodies.helper27,
    scopedHelper48 := GkrSourceBodies.scopedHelper48, helper29 := GkrSourceBodies.helper29,
    helper30 := GkrSourceBodies.helper30, helper35 := GkrSourceBodies.helper35,
    helper36 := GkrSourceBodies.helper36]

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
/-- Appending a value repeatedly uses the actual checked counted loop. -/
theorem repeat_body (table : Meanings F G) (xs : List F) (value : F) (count : Nat)
    (_small : count < indexLimit) :
    GkrSourceBodies.helper20Body.denote (meaning F G table)
      (Values.cons xs (.cons value (.cons count .nil))).get =
        .done (.cons (xs ++ List.replicate count value) .nil) := by
  simp only [GkrSourceBodies.helper20Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    show 0 < indexLimit by decide +kernel, ite_true, Values.split]
  rw [denoteLoop_states (F := F) (G := G) [.vector "bls12-381.fr"]
    [.field "bls12-381.fr"] _ count _ (.cons value .nil)
    (fun i => .cons (xs ++ List.replicate i value) .nil) ?_ ?_]
  · rfl
  · simp
  · intro i _
    change (PIR.Process.done (.cons ((xs ++ List.replicate i value) ++ [value])
      (.cons value .nil)) : Closed (Values (assignment F G)
        [.vector "bls12-381.fr", .field "bls12-381.fr"])) = _
    simp only [List.replicate_succ', List.append_assoc, Values.append]

theorem repeat_equation (xs : List F) (value : F) (count : Nat)
    (small : count < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper21Helper
      (.cons xs (.cons value (.cons count .nil))) =
        .done (.cons (xs ++ List.replicate count value) .nil) := by
  rw [helper21_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper20Helper
    (.cons xs (.cons value (.cons count .nil)))).bind _ = _
  rw [helper20_association.invoke unit.linked, repeat_body _ xs value count small]
  rfl

/-- The fold used by replication, including its concrete callback ABI. -/
abbrev replicateFold : FoldSpec :=
  (fold? GkrSourceBodies.scopedHelper45Body).get (by decide +kernel)

theorem replicate_step (xs : List F) (value : F) (source : List F) (count : Nat)
    (small : count < indexLimit) :
    invoke (helpers (G := G)) replicateFold.stepHelper
      (.cons xs (.cons value (.cons source (.cons count .nil)))) =
        .done (.cons (xs ++ List.replicate count value) .nil) := by
  change invoke (helpers (G := G)) GkrSourceBodies.helper22Helper
    (.cons xs (.cons value (.cons source (.cons count .nil)))) = _
  rw [helper22_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper21Helper
    (.cons xs (.cons value (.cons count .nil)))).bind _ = _
  rw [repeat_equation xs value count small]
  rfl

private def replicateTransition (count : Nat)
    (state : Values (assignment F G) replicateFold.state) (value : F) :
    Values (assignment F G) replicateFold.state :=
  .cons (state.get .here ++ List.replicate count value) .nil

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem replicateTransition_fold (source xs : List F) (count : Nat) :
    source.foldl (replicateTransition (G := G) count) (.cons xs .nil) =
      .cons (xs ++ source.flatMap (List.replicate count)) .nil := by
  induction source generalizing xs with
  | nil => simp
  | cons a rest ih =>
    simpa [replicateTransition, Values.get, List.append_assoc] using
      ih (xs ++ List.replicate count a)

theorem replicate_fold (source xs : List F) (count : Nat)
    (sourceBound : source.length < indexLimit) (small : count < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper45Helper
      (.cons source (.cons xs (.cons count .nil))) =
        .done (.cons (xs ++ source.flatMap (List.replicate count)) .nil) := by
  rw [scopedHelper45_association.invoke unit.linked]
  change (Evaluation.denoteFold _ replicateFold
    ((Values.cons source .nil).append ((Values.cons xs .nil).append (.cons count .nil)))).bind _ = _
  rw [Evaluation.denoteFold_reference_map (helpers (F := F) (G := G)) replicateFold
    (.cons source .nil) (.cons xs .nil) (.cons count .nil) source
    (fun value => .cons value .nil)
    (Evaluation.elements_admit _ _ _ _ _ sourceBound)
    (replicateTransition count) (fun _ => True) trivial (by
      intro state value _ _
      rw [Evaluation.foldTransition_unfiltered _ _ rfl]
      rcases state with _ | ⟨current, _ | _⟩
      exact ⟨replicate_step current value source count small, trivial⟩)]
  rw [replicateTransition_fold]
  rfl

theorem replicate_equation (source : List F) (count : Nat)
    (sourceBound : source.length < indexLimit) (small : count < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper25Helper (.cons source (.cons count .nil)) =
      .done (.cons (source.flatMap (List.replicate count)) .nil) := by
  rw [helper25_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper24Helper
    (.cons [] (.cons count (.cons source .nil)))).bind _ = _
  rw [helper24_association.invoke unit.linked]
  change ((invoke (helpers (G := G)) GkrSourceBodies.scopedHelper45Helper
    (.cons source (.cons [] (.cons count .nil)))).bind _).bind _ = _
  rw [replicate_fold source [] count sourceBound small]
  rfl

/-- The concatenation fold's ABI comes from the admitted source body. -/
abbrev appendFold : FoldSpec :=
  (fold? GkrSourceBodies.scopedHelper48Body).get (by decide +kernel)

theorem append_step (xs : List F) (value : F) (source : List F) :
    invoke (helpers (G := G)) appendFold.stepHelper
      (.cons xs (.cons value (.cons source .nil))) =
        .done (.cons (xs ++ [value]) .nil) := by
  change invoke (helpers (G := G)) GkrSourceBodies.helper27Helper
    (.cons xs (.cons value (.cons source .nil))) = _
  rw [helper27_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper26Helper
    (.cons xs (.cons value .nil))).bind _ = _
  rw [helper26_association.invoke unit.linked]
  rfl

private def appendTransition
    (state : Values (assignment F G) appendFold.state) (value : F) :
    Values (assignment F G) appendFold.state := .cons (state.get .here ++ [value]) .nil

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem appendTransition_fold (source xs : List F) :
    source.foldl (appendTransition (G := G)) (.cons xs .nil) = .cons (xs ++ source) .nil := by
  induction source generalizing xs with
  | nil => simp
  | cons a rest ih =>
    simpa [appendTransition, Values.get, List.append_assoc] using ih (xs ++ [a])

theorem append_fold (source xs : List F) (sourceBound : source.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper48Helper (.cons source (.cons xs .nil)) =
      .done (.cons (xs ++ source) .nil) := by
  rw [scopedHelper48_association.invoke unit.linked]
  change (Evaluation.denoteFold _ appendFold
    ((Values.cons source .nil).append ((Values.cons xs .nil).append .nil))).bind _ = _
  rw [Evaluation.denoteFold_reference_map (helpers (F := F) (G := G)) appendFold
    (.cons source .nil) (.cons xs .nil) .nil source
    (fun value => .cons value .nil)
    (Evaluation.elements_admit _ _ _ _ _ sourceBound)
    appendTransition (fun _ => True) trivial (by
      intro state value _ _
      rw [Evaluation.foldTransition_unfiltered _ _ rfl]
      rcases state with _ | ⟨current, _ | _⟩
      exact ⟨append_step current value source, trivial⟩)]
  rw [appendTransition_fold]
  rfl

theorem concatenate_equation (xs source : List F) (sourceBound : source.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper29Helper (.cons xs (.cons source .nil)) =
      .done (.cons (xs ++ source) .nil) := by
  rw [helper29_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.scopedHelper48Helper
    (.cons source (.cons xs .nil))).bind _ = _
  rw [append_fold source xs sourceBound]
  rfl

theorem tile_body (source : List F) (count : Nat) (_small : count < indexLimit)
    (sourceBound : source.length < indexLimit) :
    GkrSourceBodies.helper30Body.denote (meaning F G (helpers (F := F) (G := G)))
      (Values.cons source (.cons count .nil)).get =
        .done (.cons (List.replicate count source).flatten .nil) := by
  simp only [GkrSourceBodies.helper30Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    show 0 < indexLimit by decide +kernel, ite_true, Values.split]
  rw [denoteLoop_states (F := F) (G := G) [.vector "bls12-381.fr"]
    [.vector "bls12-381.fr"] _ count _ (.cons source .nil)
    (fun i => .cons (List.replicate i source).flatten .nil) ?_ ?_]
  · rfl
  · rfl
  · intro i _
    simp only [Evaluation.invokeCallback, Values.append]
    change (invoke (helpers (G := G)) GkrSourceBodies.helper29Helper
      (.cons (List.replicate i source).flatten (.cons source .nil))).bind _ = _
    rw [concatenate_equation _ source sourceBound]
    change (PIR.Process.done (.cons ((List.replicate i source).flatten ++ source)
      (.cons source .nil)) : Closed (Values (assignment F G)
        [.vector "bls12-381.fr", .vector "bls12-381.fr"])) = _
    simp only [List.replicate_succ', List.flatten_append, List.flatten_singleton]

theorem tile_equation (source : List F) (count : Nat) (small : count < indexLimit)
    (sourceBound : source.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper30Helper (.cons source (.cons count .nil)) =
      .done (.cons (List.replicate count source).flatten .nil) :=
  (helper30_association.invoke unit.linked _).trans (tile_body source count small sourceBound)

theorem prefix_body (table : Meanings F G) (xs point : List F) (dimension : Nat) :
    GkrSourceBodies.helper35Body.denote (meaning F G table)
      (Values.cons xs (.cons dimension (.cons point .nil))).get =
      (invoke table MapFirstBodies.tableHelper (inputs xs dimension 1)).bind fun selected =>
      (invoke table MapPrefixBodies.prefixHelper
        (.cons (selected.get .here) (.cons (selected.get (.there .here))
          (.cons (selected.get (.there (.there .here))) (.cons point .nil))))).bind fun fixed =>
      (invoke table MapPrefixBodies.valuesRealizationHelper
        (.cons (fixed.get .here) (.cons (fixed.get (.there .here))
          (.cons (fixed.get (.there (.there .here))) .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

/-- Prefix restriction through the producer's wrapper, with all shape checks. -/
theorem prefix_equation (xs point : List F) (dimension : Nat)
    (shape : HasShape xs dimension 1)
    (xsBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (pointBound : point.length < indexLimit) (inside : point.length ≤ dimension) :
    invoke (helpers (G := G)) GkrSourceBodies.helper35Helper
      (.cons xs (.cons dimension (.cons point .nil))) =
        .done (.cons (restrictPrefixValues xs point) .nil) := by
  rw [helper35_association.invoke unit.linked, prefix_body]
  rw [prefix_laws.tableLaw xs dimension 1 xsBound dimensionBound (by decide +kernel),
    ite_eq_left shape]
  change (invoke (helpers (G := G)) MapPrefixBodies.prefixHelper
    (MapPrefixLaws.prefixInputs xs dimension 1 point)).bind _ = _
  rw [prefix_laws.fixPrefix xs dimension 1 point shape xsBound pointBound, ite_eq_left inside]
  change (invoke (helpers (G := G)) MapPrefixBodies.valuesRealizationHelper
    (inputs (restrictPrefixValues xs point) (dimension - point.length) 1)).bind _ = _
  rw [prefix_laws.values]
  rfl

theorem layout_body (table : Meanings F G) (add mul below point : List F) (width : Nat) :
    GkrSourceBodies.helper36Body.denote (meaning F G table)
      (Values.cons add (.cons mul (.cons point (.cons below (.cons width .nil))))).get =
      (invoke table GkrSourceBodies.helper18Helper (.cons width .nil)).bind fun count =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorLength "bls12-381.fr")
        (.cons point .nil))).bind fun size =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexAdd
        (.cons (size.get .here) (.cons width .nil)))).bind fun first =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexAdd
        (.cons (first.get .here) (.cons width .nil)))).bind fun dimension =>
      (invoke table GkrSourceBodies.helper35Helper
        (.cons add (.cons (dimension.get .here) (.cons point .nil)))).bind fun a =>
      (invoke table GkrSourceBodies.helper35Helper
        (.cons mul (.cons (dimension.get .here) (.cons point .nil)))).bind fun m =>
      (invoke table GkrSourceBodies.helper25Helper
        (.cons below (.cons (count.get .here) .nil))).bind fun l =>
      (invoke table GkrSourceBodies.helper30Helper
        (.cons below (.cons (count.get .here) .nil))).bind fun r =>
      .done (.cons (a.get .here) (.cons (m.get .here) (.cons (l.get .here) (.cons (r.get .here) .nil)))) := by
  derive_process

/-- All four outputs of the actual `layer_gates` helper, in source order. -/
theorem layout_equation (add mul below point : List F) (width : Nat)
    (widthSmall : width < 64)
    (addShape : HasShape add (point.length + width + width) 1)
    (mulShape : HasShape mul (point.length + width + width) 1)
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (belowBound : below.length < indexLimit)
    (dimensionBound : point.length + width + width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper36Helper
      (.cons add (.cons mul (.cons point (.cons below (.cons width .nil))))) =
        .done (.cons (restrictPrefixValues add point)
          (.cons (restrictPrefixValues mul point)
            (.cons (below.flatMap (List.replicate (2 ^ width)))
              (.cons (List.replicate (2 ^ width) below).flatten .nil)))) := by
  have pointBound : point.length < indexLimit := by omega
  have sumBound : point.length + width < indexLimit := by omega
  have powerBound : 2 ^ width < indexLimit := by
    exact Nat.pow_lt_pow_right (by decide) widthSmall
  have widthBound : width < indexLimit := by omega
  rw [helper36_association.invoke unit.linked, layout_body, powerOfTwo_equation width widthSmall]
  simp only [PIR.Process.bind, Values.get, Primitive.evaluate, primitiveOutcome,
    checkedIndices, pointBound, sumBound, dimensionBound, widthBound, ite_true, and_self]
  rw [prefix_equation add point _ addShape addBound dimensionBound pointBound (by omega)]
  simp only [PIR.Process.bind, Values.get, inputs]
  rw [prefix_equation mul point _ mulShape mulBound dimensionBound pointBound (by omega)]
  simp only [PIR.Process.bind, Values.get]
  rw [replicate_equation below _ belowBound powerBound]
  simp only [PIR.Process.bind, Values.get]
  rw [tile_equation below _ powerBound belowBound]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestHelpers
