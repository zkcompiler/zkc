module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
public import ZkcSecurity.Bindings.Gkr.RoundsHelpers
public import Zkc.Protocols.AlgebraicRounds.Gate
public import Zkc.Source.Structured.CollectionReferenceLaws
public import Zkc.Source.TypedABI
public import ZkcSecurity.Bindings.Gkr.RoundsLayout

@[expose] public section

/-! Exact helper-body laws for the fresh actual GKR import. Selection is by
checked declaration membership, signature and entire body, never by a helper
name. Logical index capacity is the source map's existing u64 admission. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.GkrSourceViews
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
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

theorem gateValuesLeft_body (args : Values (assignment F G) gateValuesLeftHelper.inputs) :
    invoke table gateValuesLeftHelper args =
      gateValuesLeftBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateValuesLeft_closed args

theorem gateValuesRight_body (args : Values (assignment F G) gateValuesRightHelper.inputs) :
    invoke table gateValuesRightHelper args =
      gateValuesRightBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateValuesRight_closed args

theorem gateValueCallback_body (args : Values (assignment F G) gateValueCallbackHelper.inputs) :
    invoke table gateValueCallbackHelper args =
      gateValueCallbackBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateValueCallback_closed args

theorem gateValueRealization_body (args : Values (assignment F G) gateValueRealizationHelper.inputs) :
    invoke table gateValueRealizationHelper args =
      gateValueRealizationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateValueRealization_closed args

theorem gateQuadraticCallback_body (args : Values (assignment F G) gateQuadraticCallbackHelper.inputs) :
    invoke table gateQuadraticCallbackHelper args =
      gateQuadraticCallbackBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateQuadraticCallback_closed args

theorem gateQuadraticRealization_body (args : Values (assignment F G) gateQuadraticRealizationHelper.inputs) :
    invoke table gateQuadraticRealizationHelper args =
      gateQuadraticRealizationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.gateQuadraticRealization_closed args

theorem interpolationCallback_body (args : Values (assignment F G) interpolationCallbackHelper.inputs) :
    invoke table interpolationCallbackHelper args =
      interpolationCallbackBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.interpolationCallback_closed args

theorem interpolationRealization_body (args : Values (assignment F G) interpolationRealizationHelper.inputs) :
    invoke table interpolationRealizationHelper args =
      interpolationRealizationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.interpolationRealization_closed args

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

theorem values_callback (x0 x1 x2 x3 : F) (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValueCallbackHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))))))) =
      .done (.cons (Gate.value x0 x1 x2 x3) .nil) := by
  rw [gateValueCallback_body]
  change (invoke table gateValueRealizationHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 .nil))))).bind _ = _
  rw [gateValueRealization_body]
  change ((invoke table gateValueHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 .nil))))).bind _).bind _ = _
  rw [value]
  rfl

theorem collect_values (v0 v1 v2 v3 : List F) :
    Evaluation.denoteCollect (table (G := G)) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) := by
  have domain := values_domain (G := G) v0 v1 v2 v3
  cases shape : Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] with
  | stopped reason =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_admission_stop (table (G := G)) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) .nil reason domain
  | returned length =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_reference (table (G := G)) gateValuesLeftCollection
        (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) .nil (List.range length) (fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) .nil))))) domain rfl
        (valuesFormula (F := F) v0 v1 v2 v3) (fun i _ => values_callback (F := F) (G := G) (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) v0 v1 v2 v3)

theorem map_values_left (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValuesLeftHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) := by
  rw [gateValuesLeft_body]
  change (Evaluation.denoteCollect table gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))).bind _ = _
  rw [collect_values]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] <;> rfl

theorem map_values_right (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValuesRightHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) := by
  rw [gateValuesRight_body]
  change (Evaluation.denoteCollect table gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))).bind _ = _
  rw [collect_values]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] <;> rfl

theorem quadratics_callback (x0 x1 x2 x3 x4 x5 x6 x7 : F) (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G)) gateQuadraticCallbackHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))))))))))) =
      .done (.cons (Gate.quadratic x0 x1 x2 x3 x4 x5 x6 x7) .nil) := by
  rw [gateQuadraticCallback_body]
  change (invoke table gateQuadraticRealizationHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 .nil))))))))).bind _ = _
  rw [gateQuadraticRealization_body]
  change ((invoke table gateQuadraticHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 .nil))))))))).bind _).bind _ = _
  rw [quadratic]
  rfl

theorem collect_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    Evaluation.denoteCollect (table (G := G)) gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) := by
  have domain := quadratics_domain (G := G) v0 v1 v2 v3 v4 v5 v6 v7
  cases shape : Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length] with
  | stopped reason =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_admission_stop (table (G := G)) gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) .nil reason domain
  | returned length =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_reference (table (G := G)) gateQuadraticsCollection
        (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) .nil (List.range length) (fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.cons (v4[i]?.getD 0) (.cons (v5[i]?.getD 0) (.cons (v6[i]?.getD 0) (.cons (v7[i]?.getD 0) .nil))))))))) domain rfl
        (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) (fun i _ => quadratics_callback (F := F) (G := G) (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) (v4[i]?.getD 0) (v5[i]?.getD 0) (v6[i]?.getD 0) (v7[i]?.getD 0) v0 v1 v2 v3 v4 v5 v6 v7)

theorem map_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G)) gateQuadraticsHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) := by
  rw [gate_quadratics_body]
  change (Evaluation.denoteCollect table gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil))))))))).bind _ = _
  rw [collect_quadratics]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length] <;> rfl

end
end ZkcSecurity.Examples.Components.GkrRoundsHelpers
