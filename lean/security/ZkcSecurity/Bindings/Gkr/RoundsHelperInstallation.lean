module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.Participant
public import ZkcSecurity.Bindings.Gkr.RoundsHelpers
public import Zkc.Protocols.AlgebraicRounds.Gate
public import Zkc.Source.Structured.CollectionReferenceLaws
public import Zkc.Source.TypedABI
public import ZkcSecurity.Bindings.Gkr.RoundsLayout

@[expose] public section

set_option autoImplicit false

/-! Exact GKR helper installation on any linked definition list. Each dependency
is associated by complete signature and raw body. Collection admission and all
stopping outcomes remain in the resulting Process equations. -/

namespace ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Examples.Components.GkrRoundsHelpers
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false

noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

structure RestrictionBodies (definitions : List CheckedDefinition) : Prop where
  interpolation : BodyIn definitions interpolationHelper interpolationBody
  interpolations : BodyIn definitions interpolationsHelper interpolationsBody
  factor_restriction : BodyIn definitions factorRestrictionHelper factorRestrictionBody
  interpolationCallback : BodyIn definitions interpolationCallbackHelper interpolationCallbackBody
  interpolationRealization : BodyIn definitions interpolationRealizationHelper interpolationRealizationBody

structure Bodies (definitions : List CheckedDefinition) : Prop
    extends RestrictionBodies definitions where
  gate_value : BodyIn definitions gateValueHelper gateValueBody
  gate_quadratic : BodyIn definitions gateQuadraticHelper gateQuadraticBody
  gate_quadratics : BodyIn definitions gateQuadraticsHelper gateQuadraticsBody
  linear_coefficient : BodyIn definitions linearCoefficientHelper linearCoefficientBody
  linear_wrapper : BodyIn definitions linearWrapperHelper linearWrapperBody
  round_message : BodyIn definitions roundMessageHelper roundMessageBody
  gate_restriction : BodyIn definitions gateRestrictionHelper gateRestrictionBody
  gateValuesLeft : BodyIn definitions gateValuesLeftHelper gateValuesLeftBody
  gateValuesRight : BodyIn definitions gateValuesRightHelper gateValuesRightBody
  gateValueCallback : BodyIn definitions gateValueCallbackHelper gateValueCallbackBody
  gateValueRealization : BodyIn definitions gateValueRealizationHelper gateValueRealizationBody
  gateQuadraticCallback : BodyIn definitions gateQuadraticCallbackHelper gateQuadraticCallbackBody
  gateQuadraticRealization : BodyIn definitions gateQuadraticRealizationHelper gateQuadraticRealizationBody

variable {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions)
include linked bodies

/-- The actual silent helper fold, retaining each definition's captured prefix. -/
abbrev table (definitions : List CheckedDefinition) :
    HelperTable (assignment F G) (participantInterface F G) :=
  definitions.foldl (Evaluation.extendMeanings (.silent _)) []

theorem gate_value_body (args : Values (assignment F G) gateValueHelper.inputs) :
    invoke (table definitions) gateValueHelper args =
      gateValueBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gate_value
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateValueHelper signature gateValueBody exactRaw args

theorem gate_quadratic_body (args : Values (assignment F G) gateQuadraticHelper.inputs) :
    invoke (table definitions) gateQuadraticHelper args =
      gateQuadraticBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gate_quadratic
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateQuadraticHelper signature gateQuadraticBody exactRaw args

theorem gate_quadratics_body (args : Values (assignment F G) gateQuadraticsHelper.inputs) :
    invoke (table definitions) gateQuadraticsHelper args =
      gateQuadraticsBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gate_quadratics
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateQuadraticsHelper signature gateQuadraticsBody exactRaw args

theorem linear_coefficient_body (args : Values (assignment F G) linearCoefficientHelper.inputs) :
    invoke (table definitions) linearCoefficientHelper args =
      linearCoefficientBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.linear_coefficient
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member linearCoefficientHelper signature linearCoefficientBody exactRaw args

theorem linear_wrapper_body (args : Values (assignment F G) linearWrapperHelper.inputs) :
    invoke (table definitions) linearWrapperHelper args =
      linearWrapperBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.linear_wrapper
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member linearWrapperHelper signature linearWrapperBody exactRaw args

theorem round_message_body (args : Values (assignment F G) roundMessageHelper.inputs) :
    invoke (table definitions) roundMessageHelper args =
      roundMessageBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.round_message
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member roundMessageHelper signature roundMessageBody exactRaw args

omit bodies in
theorem interpolation_body (bodies : RestrictionBodies definitions) (args : Values (assignment F G) interpolationHelper.inputs) :
    invoke (table definitions) interpolationHelper args =
      interpolationBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.interpolation
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member interpolationHelper signature interpolationBody exactRaw args

omit bodies in
theorem interpolations_body (bodies : RestrictionBodies definitions) (args : Values (assignment F G) interpolationsHelper.inputs) :
    invoke (table definitions) interpolationsHelper args =
      interpolationsBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.interpolations
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member interpolationsHelper signature interpolationsBody exactRaw args

omit bodies in
theorem factor_restriction_body (bodies : RestrictionBodies definitions) (args : Values (assignment F G) factorRestrictionHelper.inputs) :
    invoke (table definitions) factorRestrictionHelper args =
      factorRestrictionBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.factor_restriction
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member factorRestrictionHelper signature factorRestrictionBody exactRaw args

theorem gate_restriction_body (args : Values (assignment F G) gateRestrictionHelper.inputs) :
    invoke (table definitions) gateRestrictionHelper args =
      gateRestrictionBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gate_restriction
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateRestrictionHelper signature gateRestrictionBody exactRaw args

theorem gateValuesLeft_body (args : Values (assignment F G) gateValuesLeftHelper.inputs) :
    invoke (table definitions) gateValuesLeftHelper args =
      gateValuesLeftBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gateValuesLeft
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateValuesLeftHelper signature gateValuesLeftBody exactRaw args

theorem gateValuesRight_body (args : Values (assignment F G) gateValuesRightHelper.inputs) :
    invoke (table definitions) gateValuesRightHelper args =
      gateValuesRightBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gateValuesRight
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateValuesRightHelper signature gateValuesRightBody exactRaw args

theorem gateValueCallback_body (args : Values (assignment F G) gateValueCallbackHelper.inputs) :
    invoke (table definitions) gateValueCallbackHelper args =
      gateValueCallbackBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gateValueCallback
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateValueCallbackHelper signature gateValueCallbackBody exactRaw args

theorem gateValueRealization_body (args : Values (assignment F G) gateValueRealizationHelper.inputs) :
    invoke (table definitions) gateValueRealizationHelper args =
      gateValueRealizationBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gateValueRealization
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateValueRealizationHelper signature gateValueRealizationBody exactRaw args

theorem gateQuadraticCallback_body (args : Values (assignment F G) gateQuadraticCallbackHelper.inputs) :
    invoke (table definitions) gateQuadraticCallbackHelper args =
      gateQuadraticCallbackBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gateQuadraticCallback
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateQuadraticCallbackHelper signature gateQuadraticCallbackBody exactRaw args

theorem gateQuadraticRealization_body (args : Values (assignment F G) gateQuadraticRealizationHelper.inputs) :
    invoke (table definitions) gateQuadraticRealizationHelper args =
      gateQuadraticRealizationBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.gateQuadraticRealization
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member gateQuadraticRealizationHelper signature gateQuadraticRealizationBody exactRaw args

omit bodies in
theorem interpolationCallback_body (bodies : RestrictionBodies definitions) (args : Values (assignment F G) interpolationCallbackHelper.inputs) :
    invoke (table definitions) interpolationCallbackHelper args =
      interpolationCallbackBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.interpolationCallback
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member interpolationCallbackHelper signature interpolationCallbackBody exactRaw args

omit bodies in
theorem interpolationRealization_body (bodies : RestrictionBodies definitions) (args : Values (assignment F G) interpolationRealizationHelper.inputs) :
    invoke (table definitions) interpolationRealizationHelper args =
      interpolationRealizationBody.denote (Evaluation.meaning (.silent _) (table definitions)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := bodies.interpolationRealization
  exact Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member interpolationRealizationHelper signature interpolationRealizationBody exactRaw args


theorem value (a m l r : F) :
    invoke (table (G := G) definitions) gateValueHelper (.cons a (.cons m (.cons l (.cons r .nil)))) =
      .done (.cons (Gate.value a m l r) .nil) := by
  rw [gate_value_body linked bodies]
  rfl

theorem quadratic (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    invoke (table (G := G) definitions) gateQuadraticHelper
      (.cons a0 (.cons a1 (.cons m0 (.cons m1 (.cons l0 (.cons l1 (.cons r0 (.cons r1 .nil)))))))) =
      .done (.cons (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1) .nil) := by
  rw [gate_quadratic_body linked bodies]
  rfl

theorem linear (a b q : F) :
    invoke (table (G := G) definitions) linearWrapperHelper (.cons a (.cons b (.cons q .nil))) =
      .done (.cons (b - a - q) .nil) := by
  rw [linear_wrapper_body linked bodies]
  change (invoke (table definitions) linearCoefficientHelper (.cons a (.cons b (.cons q .nil)))).bind _ = _
  rw [linear_coefficient_body linked bodies]
  rfl

omit bodies in
theorem interpolate (bodies : RestrictionBodies definitions) (a b r : F) :
    invoke (table (G := G) definitions) interpolationHelper (.cons a (.cons b (.cons r .nil))) =
      .done (.cons (a + (b - a) * r) .nil) := by
  rw [interpolation_body linked bodies]
  rfl

set_option smartUnfolding true

theorem values_callback (x0 x1 x2 x3 : F) (v0 v1 v2 v3 : List F) :
    invoke (table (G := G) definitions) gateValueCallbackHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))))))) =
      .done (.cons (Gate.value x0 x1 x2 x3) .nil) := by
  rw [gateValueCallback_body linked bodies]
  change (invoke (table definitions) gateValueRealizationHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 .nil))))).bind _ = _
  rw [gateValueRealization_body linked bodies]
  change ((invoke (table definitions) gateValueHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 .nil))))).bind _).bind _ = _
  rw [value linked bodies]
  rfl

theorem collect_values (v0 v1 v2 v3 : List F) :
    Evaluation.denoteCollect (table (G := G) definitions) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) := by
  have domain := values_domain (G := G) v0 v1 v2 v3
  cases shape : Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] with
  | stopped reason =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_admission_stop (table (G := G) definitions) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) .nil reason domain
  | returned length =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_reference (table (G := G) definitions) gateValuesLeftCollection
        (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) .nil (List.range length) (fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) .nil))))) domain rfl
        (valuesFormula (F := F) v0 v1 v2 v3) (fun i _ => values_callback linked bodies (F := F) (G := G) (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) v0 v1 v2 v3)

theorem map_values_left (v0 v1 v2 v3 : List F) :
    invoke (table (G := G) definitions) gateValuesLeftHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) := by
  rw [gateValuesLeft_body linked bodies]
  change (Evaluation.denoteCollect (table definitions) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))).bind _ = _
  rw [collect_values linked bodies]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] <;> rfl

theorem map_values_right (v0 v1 v2 v3 : List F) :
    invoke (table (G := G) definitions) gateValuesRightHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) := by
  rw [gateValuesRight_body linked bodies]
  change (Evaluation.denoteCollect (table definitions) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))).bind _ = _
  rw [collect_values linked bodies]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length] <;> rfl

theorem quadratics_callback (x0 x1 x2 x3 x4 x5 x6 x7 : F) (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G) definitions) gateQuadraticCallbackHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))))))))))) =
      .done (.cons (Gate.quadratic x0 x1 x2 x3 x4 x5 x6 x7) .nil) := by
  rw [gateQuadraticCallback_body linked bodies]
  change (invoke (table definitions) gateQuadraticRealizationHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 .nil))))))))).bind _ = _
  rw [gateQuadraticRealization_body linked bodies]
  change ((invoke (table definitions) gateQuadraticHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 .nil))))))))).bind _).bind _ = _
  rw [quadratic linked bodies]
  rfl

theorem collect_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    Evaluation.denoteCollect (table (G := G) definitions) gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) := by
  have domain := quadratics_domain (G := G) v0 v1 v2 v3 v4 v5 v6 v7
  cases shape : Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length] with
  | stopped reason =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_admission_stop (table (G := G) definitions) gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) .nil reason domain
  | returned length =>
    simp only [shape, Finite.continueWith] at domain
    simpa only [mapped, shape, Finite.admitThen, Values.append, Collection.pack] using
      Evaluation.denoteCollect_reference (table (G := G) definitions) gateQuadraticsCollection
        (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) .nil (List.range length) (fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.cons (v4[i]?.getD 0) (.cons (v5[i]?.getD 0) (.cons (v6[i]?.getD 0) (.cons (v7[i]?.getD 0) .nil))))))))) domain rfl
        (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) (fun i _ => quadratics_callback linked bodies (F := F) (G := G) (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) (v4[i]?.getD 0) (v5[i]?.getD 0) (v6[i]?.getD 0) (v7[i]?.getD 0) v0 v1 v2 v3 v4 v5 v6 v7)

theorem map_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G) definitions) gateQuadraticsHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) := by
  rw [gate_quadratics_body linked bodies]
  change (Evaluation.denoteCollect (table definitions) gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil))))))))).bind _ = _
  rw [collect_quadratics linked bodies]
  cases Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length] <;> rfl

end
end ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation
