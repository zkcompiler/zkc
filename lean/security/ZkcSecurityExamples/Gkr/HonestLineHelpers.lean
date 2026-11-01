module

public import ZkcSecurityExamples.Gkr.HonestHelpersReadback
public import Zkc.Polynomial.Multilinear.LineCoefficients
public import ZkcSecurityExamples.Gkr.HonestLineCompanion
public meta import ZkcTools.StructuredSource.NamedEquations

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
    helper52 := GkrSourceBodies.helper52,
    scopedHelper70 := GkrSourceBodies.scopedHelper70, helper62 := GkrSourceBodies.helper62,
    helper63 := GkrSourceBodies.helper63, scopedHelper86 := GkrSourceBodies.scopedHelper86,
    helper65 := GkrSourceBodies.helper65, helper66 := GkrSourceBodies.helper66,
    scopedHelper73 := GkrSourceBodies.scopedHelper73,
    helper69 := GkrSourceBodies.helper69]

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Collection.type Collection.element Op.arguments Op.results Op.regions

set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option maxRecDepth 20000 in
theorem scalar_bodies : Goals.ScalarBodies unit.definitions := by
  bind_structured_bodies

theorem scalar_laws : Companion.ScalarLaws (ringModel F G)
    (closedMeaningsOn (ringModel F G) unit.definitions) :=
  Companion.installScalars (ringModel F G) unit.definitions unit.linked scalar_bodies

theorem constant_row (xs : List F) (value : F) (width : Nat) (small : width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper49Helper
      (Goals.ConstantWrapper.Inputs.pack (Value := assignment F G) { initial := xs, value, width }) =
        .done (Goals.Constant.encode (ringModel F G) ⟨xs ++ (value :: List.replicate width 0)⟩) := by
  rw [helper49_association.invoke unit.linked]
  named_equation Goals.ConstantWrapper over F G
  rw [helper48_association.invoke unit.linked]
  named_equation Goals.Constant over F G
  rw [HonestHelpers.zero_equation]
  simp only [Primitive.evaluateOn, primitiveOutcome, PIR.Process.bind, Environment.prepend,
    Environment.push, Values.get_cons, Values.get]
  rw [HonestHelpers.helper20_association.invoke unit.linked]
  simp only [Values.get_cons, Values.get]
  have repeated := HonestHelpers.repeat_body (F := F) (G := G)
    (helpers (F := F) (G := G)) (xs ++ [value]) (0 : F) width small
  simp only [Values.get_cons, Environment.push] at repeated ⊢
  rw [repeated]
  simp [PIR.Process.bind, Environment.prepend, Environment.push, Values.get, List.append_assoc]

noncomputable abbrev constantFold : FoldSpec := Goals.constantSpec

theorem constant_step (xs : List F) (value : F) (source : List F) (width : Nat)
    (small : width < indexLimit) :
    invoke (helpers (G := G)) constantFold.stepHelper
      (Goals.ConstantStep.Inputs.pack (Value := assignment F G) { initial := xs, value, source, width }) =
        .done (Goals.Constant.encode (ringModel F G) ⟨xs ++ (value :: List.replicate width 0)⟩) := by
  change invoke (helpers (G := G)) GkrSourceBodies.helper50Helper _ = _
  rw [helper50_association.invoke unit.linked]
  named_equation Goals.ConstantStep over F G
  rw [constant_row xs value width small]
  rfl

theorem constant_fold (values xs : List F) (width : Nat)
    (valuesBound : values.length < indexLimit) (small : width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper80Helper
      (Goals.ConstantFold.Inputs.pack (Value := assignment F G) { source := values, initial := xs, width }) =
        .done (Goals.Constants.encode (ringModel F G) ⟨xs ++ values.flatMap (fun v => v :: List.replicate width 0)⟩) := by
  rw [scopedHelper80_association.invoke unit.linked]
  named_equation Goals.ConstantFold over F G
  have admitted : constantFold.domain.admit (Goals.ConstantDomain.pack (Value := assignment F G) ⟨values⟩) =
      .returned (values.map fun value => Goals.ConstantItem.pack ⟨value⟩) := by
    simp [constantFold, Goals.constantSpec, Goals.ConstantFold.body, GkrSourceLaws.fold?,
      GkrSourceBodies.scopedHelper80Body, DomainSpec.admit, DomainBody.admit, DomainNode.admit,
      Collection.values, Goals.ConstantDomain.pack, Goals.ConstantItem.pack, Values.get, valuesBound,
      Finite.continueWith]
  have folded := Evaluation.denoteFoldOn_append_encode (model := ringModel F G)
    (helpers (F := F) (G := G)) constantFold
    (Goals.ConstantDomain.pack ⟨values⟩) (Goals.ConstantCaptures.pack ⟨width⟩) values
    (fun value => Goals.ConstantItem.pack ⟨value⟩)
    (fun values => Goals.ConstantState.pack ⟨values⟩) xs admitted
    (fun value => value :: List.replicate width 0) (by
      intro current value
      rw [← Evaluation.foldTransition_eq_foldTransitionOn (F := F) (G := G),
        Evaluation.foldTransition_unfiltered _ _ rfl]
      exact constant_step (G := G) current value values width small)
  erw [folded]
  rfl

theorem constant_rows (values xs : List F) (width : Nat)
    (valuesBound : values.length < indexLimit) (small : width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper52Helper
      (Goals.Constants.Inputs.pack (Value := assignment F G) { initial := xs, width, source := values }) =
        .done (Goals.Constants.encode (ringModel F G) ⟨xs ++ values.flatMap (fun v => v :: List.replicate width 0)⟩) := by
  rw [helper52_association.invoke unit.linked]
  named_equation Goals.Constants over F G
  rw [constant_fold values xs width valuesBound small]
  rfl

theorem difference (high low : F) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper67Helper (Goals.DifferenceWrapper.Inputs.pack (Value := assignment F G) { high, low }) =
      .done (Goals.DifferenceWrapper.encode (ringModel F G) ⟨high - low⟩) := by
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  simpa [Companion.differenceWrapperLaw, Goals.DifferenceWrapper.law,
    Companion.differenceWrapperReference, Goals.DifferenceWrapper.Inputs.pack,
    Goals.DifferenceWrapper.encodeOutcome, Goals.DifferenceWrapper.encode, primitiveOutcome] using
    (scalar_laws (F := F) (G := G)).differenceWrapper
      (Goals.DifferenceWrapper.Inputs.pack { high, low })

noncomputable abbrev slopeCollection : CollectSpec := Goals.slopesSpec
noncomputable abbrev totalCollection : CollectSpec := Goals.totalsSpec

noncomputable abbrev slopeBindings : MultilinearCollectBodies.Bindings :=
  ⟨GkrSourceBodies.scopedHelper70Helper.name, slopeCollection.domain.name,
    slopeCollection.body, GkrSourceBodies.scopedHelper68Helper.name⟩
noncomputable abbrev totalBindings : MultilinearCollectBodies.Bindings :=
  ⟨GkrSourceBodies.scopedHelper73Helper.name, totalCollection.domain.name,
    totalCollection.body, GkrSourceBodies.scopedHelper71Helper.name⟩

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [scopedHelper66 := GkrSourceBodies.scopedHelper66]

theorem slope_map (left right : List F) (delta : F)
    (small : left.length < indexLimit) (same : right.length = left.length) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper70Helper
      (Goals.Slopes.Inputs.pack (Value := assignment F G) { left, right, delta }) =
        .done (Goals.Slopes.encode (ringModel F G) ⟨List.zipWith (fun a b => (b - a) * delta) left right⟩) := by
  rw [scopedHelper70_association.invoke unit.linked]
  named_equation Goals.Slopes over F G
  have collected := Evaluation.denoteCollect_reference (helpers (F := F) (G := G)) slopeCollection
    (Goals.SlopesDomain.pack ⟨left, right⟩) (Goals.SlopesCaptures.pack ⟨delta⟩) (left.zip right)
    (fun pair => Goals.SlopesItem.pack ⟨pair.1, pair.2⟩)
    (MultilinearCollectLaws.domain_admit slopeBindings left right small same.symm) rfl
    (fun pair => (pair.2 - pair.1) * delta) (by
      intro pair _
      change invoke (helpers (F := F) (G := G)) GkrSourceBodies.scopedHelper69Helper _ = _
      simpa [Goals.SlopesItem.pack, Goals.SlopesDomain.pack, Goals.SlopesCaptures.pack,
        Values.append, closedMeanings_eq_closedMeaningsOn, Companion.slopeCallbackLaw,
        Goals.SlopeCallback.law, Companion.slopeCallbackReference, Goals.SlopeCallback.Inputs.pack,
        Goals.SlopeCallback.encodeOutcome, Goals.SlopeCallback.encode, primitiveOutcome] using
        (scalar_laws (F := F) (G := G)).slopeCallback
          (Goals.SlopeCallback.Inputs.pack { low := pair.1, high := pair.2, left, right, delta }))
  simp only [Goals.SlopesDomain.pack, Goals.SlopesCaptures.pack, Goals.SlopesItem.pack, Values.append] at collected
  rw [collected]
  simp only [PIR.Process.bind, Values.get, Collection.pack, List.map_zip_eq_zipWith]
  rfl

theorem total_map (left right : List F)
    (small : left.length < indexLimit) (same : right.length = left.length) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper73Helper (Goals.Totals.Inputs.pack (Value := assignment F G) { left, right }) =
      .done (Goals.Totals.encode (ringModel F G) ⟨List.zipWith (· + ·) left right⟩) := by
  rw [scopedHelper73_association.invoke unit.linked]
  named_equation Goals.Totals over F G
  have collected := Evaluation.denoteCollect_reference (helpers (F := F) (G := G)) totalCollection
    (Goals.TotalsDomain.pack ⟨left, right⟩) .nil (left.zip right)
    (fun pair => Goals.TotalsItem.pack ⟨pair.1, pair.2⟩)
    (MultilinearCollectLaws.domain_admit totalBindings left right small same.symm) rfl
    (fun pair => pair.1 + pair.2) (by
      intro pair _
      change invoke (helpers (F := F) (G := G)) GkrSourceBodies.scopedHelper72Helper _ = _
      simpa [Goals.TotalsItem.pack, Goals.TotalsDomain.pack,
        Values.append, closedMeanings_eq_closedMeaningsOn, Companion.totalCallbackLaw,
        Goals.TotalCallback.law, Companion.totalCallbackReference, Goals.TotalCallback.Inputs.pack,
        Goals.TotalCallback.encodeOutcome, Goals.TotalCallback.encode, primitiveOutcome] using
        (scalar_laws (F := F) (G := G)).totalCallback
          (Goals.TotalCallback.Inputs.pack { low := pair.1, high := pair.2, left, right }))
  simp only [Goals.TotalsDomain.pack, Goals.TotalsItem.pack, Values.append] at collected
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
