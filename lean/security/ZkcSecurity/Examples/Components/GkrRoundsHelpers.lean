module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
public import Zkc.Source.Structured.MapLaws
public import ZkcSecurity.Examples.Components.GkrRoundsLayout

@[expose] public section

/-! Exact helper-body laws for the fresh actual GKR import. Selection is by
checked declaration membership, signature and entire body, never by a helper
name. Logical index capacity is the source map's existing u64 admission. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

export ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
  (emptyHelper emptyBody appendHelper appendBody gateValueHelper gateValueBody gateValuesHelper gateValuesBody gateQuadraticHelper gateQuadraticBody gateQuadraticsHelper gateQuadraticsBody linearCoefficientHelper linearCoefficientBody linearWrapperHelper linearWrapperBody roundMessageHelper roundMessageBody interpolationHelper interpolationBody interpolationsHelper interpolationsBody factorRestrictionHelper factorRestrictionBody gateRestrictionHelper gateRestrictionBody)

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false

noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev table : HelperTable (assignment F G) (participantInterface F G) :=
  payload.definitions.foldl (Evaluation.extendMeanings (.silent _)) []

theorem gate_value_body (args : Values (assignment F G) gateValueHelper.inputs) :
    invoke table gateValueHelper args =
      gateValueBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateValue_closed args

theorem gate_values_body (args : Values (assignment F G) gateValuesHelper.inputs) :
    invoke table gateValuesHelper args =
      gateValuesBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateValues_closed args

theorem gate_quadratic_body (args : Values (assignment F G) gateQuadraticHelper.inputs) :
    invoke table gateQuadraticHelper args =
      gateQuadraticBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateQuadratic_closed args

theorem gate_quadratics_body (args : Values (assignment F G) gateQuadraticsHelper.inputs) :
    invoke table gateQuadraticsHelper args =
      gateQuadraticsBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateQuadratics_closed args

theorem linear_coefficient_body (args : Values (assignment F G) linearCoefficientHelper.inputs) :
    invoke table linearCoefficientHelper args =
      linearCoefficientBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.linearCoefficient_closed args

theorem linear_wrapper_body (args : Values (assignment F G) linearWrapperHelper.inputs) :
    invoke table linearWrapperHelper args =
      linearWrapperBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.linearWrapper_closed args

theorem round_message_body (args : Values (assignment F G) roundMessageHelper.inputs) :
    invoke table roundMessageHelper args =
      roundMessageBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.roundMessage_closed args

theorem interpolation_body (args : Values (assignment F G) interpolationHelper.inputs) :
    invoke table interpolationHelper args =
      interpolationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.interpolation_closed args

theorem interpolations_body (args : Values (assignment F G) interpolationsHelper.inputs) :
    invoke table interpolationsHelper args =
      interpolationsBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.interpolations_closed args

theorem factor_restriction_body (args : Values (assignment F G) factorRestrictionHelper.inputs) :
    invoke table factorRestrictionHelper args =
      factorRestrictionBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.factorRestriction_closed args

theorem gate_restriction_body (args : Values (assignment F G) gateRestrictionHelper.inputs) :
    invoke table gateRestrictionHelper args =
      gateRestrictionBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateRestriction_closed args

theorem value (a m l r : F) :
    invoke (table (G := G)) gateValueHelper (.cons a (.cons m (.cons l (.cons r .nil)))) =
      .done (.cons (Gate.value a m l r) .nil) := by
  rw [gate_value_body]
  rfl

theorem quadratic (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    invoke (table (G := G)) gateQuadraticHelper
      (.cons a0 (.cons a1 (.cons m0 (.cons m1 (.cons l0 (.cons l1 (.cons r0 (.cons r1 .nil)))))))) =
      .done (.cons (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1) .nil) := by
  rw [gate_quadratic_body]
  rfl

theorem linear (a b q : F) :
    invoke (table (G := G)) linearWrapperHelper (.cons a (.cons b (.cons q .nil))) =
      .done (.cons (b - a - q) .nil) := by
  rw [linear_wrapper_body]
  change (invoke table linearCoefficientHelper (.cons a (.cons b (.cons q .nil)))).bind _ = _
  rw [linear_coefficient_body]
  rfl

theorem interpolate (a b r : F) :
    invoke (table (G := G)) interpolationHelper (.cons a (.cons b (.cons r .nil))) =
      .done (.cons (a + (b - a) * r) .nil) := by
  rw [interpolation_body]
  rfl

set_option smartUnfolding true

/-- A successful source map has checked every row, in operand order. -/
theorem remaining_shape {expected length : Nat} {rows : List Nat}
    (ok : Evaluation.mapShapeRemaining expected rows = .returned length) :
    length = expected ∧ ∀ k ∈ rows, k = expected ∧ k < indexLimit := by
  induction rows with
  | nil => exact ⟨(PIR.Outcome.returned.inj ok).symm, by simp⟩
  | cons row rows ih =>
    simp only [Evaluation.mapShapeRemaining] at ok
    split at ok
    · split at ok
      · obtain ⟨rfl, rest⟩ := ih ok
        refine ⟨rfl, ?_⟩
        intro k member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨by assumption, by assumption⟩
        · exact rest k member
      · contradiction
    · contradiction

theorem admitted_shape {rows : List Nat} {length : Nat}
    (ok : Evaluation.mapShape rows = .returned length) :
    ∀ k ∈ rows, k = length ∧ k < indexLimit := by
  cases rows with
  | nil => contradiction
  | cons row rows =>
    simp only [Evaluation.mapShape] at ok
    split at ok
    · obtain ⟨rfl, rest⟩ := remaining_shape ok
      intro k member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl, by assumption⟩
      · exact rest k member
    · contradiction

def mapped {I : PIR.Signature} (shape : PIR.Outcome Nat) (formula : Nat → F) :
    PIR.Process I (Values (assignment F G) [.vector "bls12-381.fr"]) :=
  Finite.admitThen shape fun length => .done (.cons ((List.range length).map formula) .nil)

def valuesFormula (v0 v1 v2 v3 : List F) (i : Nat) : F :=
  Gate.value (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0)

theorem map_values (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValuesHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.nil))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula v0 v1 v2 v3) := by
  have equation : Evaluation.denoteMap (table (G := G)) ⟨gateValueHelper.name, "bls12-381.fr", [true, true, true, true]⟩ (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.nil))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula v0 v1 v2 v3) := by
    cases shape : Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] with
    | stopped reason =>
      exact Evaluation.denoteMap_shape_stops _ _ _ _ shape
    | returned length =>
      have bounds := admitted_shape shape
      have selected : ∀ i < length, Evaluation.mapRowArguments (F := F) (G := G) "bls12-381.fr"
          [true, true, true, true] (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.nil))))) i = some (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.nil))))) := by
        intro i bound
        have hv0 : i < v0.length := by have := (bounds v0.length (by simp)).1; omega
        have hv1 : i < v1.length := by have := (bounds v1.length (by simp)).1; omega
        have hv2 : i < v2.length := by have := (bounds v2.length (by simp)).1; omega
        have hv3 : i < v3.length := by have := (bounds v3.length (by simp)).1; omega
        simp only [Evaluation.mapRowArguments, List.getElem?_eq_getElem hv0, List.getElem?_eq_getElem hv1, List.getElem?_eq_getElem hv2, List.getElem?_eq_getElem hv3, Option.getD_some]
        rfl
      simpa only [mapped, shape, Finite.admitThen] using
        Evaluation.denoteMap_reference (table (G := G)) ⟨gateValueHelper.name, "bls12-381.fr", [true, true, true, true]⟩ (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.nil))))) length shape
          (fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.nil)))))) (valuesFormula v0 v1 v2 v3) selected
          (fun i _ => value (G := G) (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0))
  rw [gate_values_body]
  change (Evaluation.denoteMap (table (G := G)) ⟨gateValueHelper.name, "bls12-381.fr", [true, true, true, true]⟩ (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.nil)))))).bind _ = _
  rw [equation]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] <;> rfl

def quadraticsFormula (v0 v1 v2 v3 v4 v5 v6 v7 : List F) (i : Nat) : F :=
  Gate.quadratic (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) (v4[i]?.getD 0) (v5[i]?.getD 0) (v6[i]?.getD 0) (v7[i]?.getD 0)

theorem map_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G)) gateQuadraticsHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 (.nil))))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula v0 v1 v2 v3 v4 v5 v6 v7) := by
  have equation : Evaluation.denoteMap (table (G := G)) ⟨gateQuadraticHelper.name, "bls12-381.fr", [true, true, true, true, true, true, true, true]⟩ (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 (.nil))))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula v0 v1 v2 v3 v4 v5 v6 v7) := by
    cases shape : Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length] with
    | stopped reason =>
      exact Evaluation.denoteMap_shape_stops _ _ _ _ shape
    | returned length =>
      have bounds := admitted_shape shape
      have selected : ∀ i < length, Evaluation.mapRowArguments (F := F) (G := G) "bls12-381.fr"
          [true, true, true, true, true, true, true, true] (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 (.nil))))))))) i = some (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.cons (v4[i]?.getD 0) (.cons (v5[i]?.getD 0) (.cons (v6[i]?.getD 0) (.cons (v7[i]?.getD 0) (.nil))))))))) := by
        intro i bound
        have hv0 : i < v0.length := by have := (bounds v0.length (by simp)).1; omega
        have hv1 : i < v1.length := by have := (bounds v1.length (by simp)).1; omega
        have hv2 : i < v2.length := by have := (bounds v2.length (by simp)).1; omega
        have hv3 : i < v3.length := by have := (bounds v3.length (by simp)).1; omega
        have hv4 : i < v4.length := by have := (bounds v4.length (by simp)).1; omega
        have hv5 : i < v5.length := by have := (bounds v5.length (by simp)).1; omega
        have hv6 : i < v6.length := by have := (bounds v6.length (by simp)).1; omega
        have hv7 : i < v7.length := by have := (bounds v7.length (by simp)).1; omega
        simp only [Evaluation.mapRowArguments, List.getElem?_eq_getElem hv0, List.getElem?_eq_getElem hv1, List.getElem?_eq_getElem hv2, List.getElem?_eq_getElem hv3, List.getElem?_eq_getElem hv4, List.getElem?_eq_getElem hv5, List.getElem?_eq_getElem hv6, List.getElem?_eq_getElem hv7, Option.getD_some]
        rfl
      simpa only [mapped, shape, Finite.admitThen] using
        Evaluation.denoteMap_reference (table (G := G)) ⟨gateQuadraticHelper.name, "bls12-381.fr", [true, true, true, true, true, true, true, true]⟩ (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 (.nil))))))))) length shape
          (fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.cons (v4[i]?.getD 0) (.cons (v5[i]?.getD 0) (.cons (v6[i]?.getD 0) (.cons (v7[i]?.getD 0) (.nil)))))))))) (quadraticsFormula v0 v1 v2 v3 v4 v5 v6 v7) selected
          (fun i _ => quadratic (G := G) (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) (v4[i]?.getD 0) (v5[i]?.getD 0) (v6[i]?.getD 0) (v7[i]?.getD 0))
  rw [gate_quadratics_body]
  change (Evaluation.denoteMap (table (G := G)) ⟨gateQuadraticHelper.name, "bls12-381.fr", [true, true, true, true, true, true, true, true]⟩ (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 (.nil)))))))))).bind _ = _
  rw [equation]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length] <;> rfl

end
end ZkcSecurity.Examples.Components.GkrRoundsHelpers
