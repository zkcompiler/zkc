module

public import ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation
public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
public import Zkc.Source.Structured.BodyBindings
public import ZkcSecurity.Bindings.Gkr.RoundsHelpers
public import Zkc.Protocols.AlgebraicRounds.Gate
public import Zkc.Source.Structured.CollectionReferenceLaws
public import Zkc.Source.TypedABI
public import ZkcSecurity.Bindings.Gkr.RoundsLayout

@[expose] public section

/-! The actual GKR import installs the reusable helper laws by exact body
association. No helper mathematics is expanded in this application. -/

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

theorem bodies : ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.Bodies payload.definitions := by
  bind_structured_bodies

theorem gate_value_body (args : Values (assignment F G) gateValueHelper.inputs) :
    invoke table gateValueHelper args =
      gateValueBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gate_value_body payload.linked bodies args

theorem gate_quadratic_body (args : Values (assignment F G) gateQuadraticHelper.inputs) :
    invoke table gateQuadraticHelper args =
      gateQuadraticBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gate_quadratic_body payload.linked bodies args

theorem gate_quadratics_body (args : Values (assignment F G) gateQuadraticsHelper.inputs) :
    invoke table gateQuadraticsHelper args =
      gateQuadraticsBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gate_quadratics_body payload.linked bodies args

theorem linear_coefficient_body (args : Values (assignment F G) linearCoefficientHelper.inputs) :
    invoke table linearCoefficientHelper args =
      linearCoefficientBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.linear_coefficient_body payload.linked bodies args

theorem linear_wrapper_body (args : Values (assignment F G) linearWrapperHelper.inputs) :
    invoke table linearWrapperHelper args =
      linearWrapperBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.linear_wrapper_body payload.linked bodies args

theorem round_message_body (args : Values (assignment F G) roundMessageHelper.inputs) :
    invoke table roundMessageHelper args =
      roundMessageBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.round_message_body payload.linked bodies args

theorem interpolation_body (args : Values (assignment F G) interpolationHelper.inputs) :
    invoke table interpolationHelper args =
      interpolationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.interpolation_body payload.linked bodies.toRestrictionBodies args

theorem interpolations_body (args : Values (assignment F G) interpolationsHelper.inputs) :
    invoke table interpolationsHelper args =
      interpolationsBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.interpolations_body payload.linked bodies.toRestrictionBodies args

theorem factor_restriction_body (args : Values (assignment F G) factorRestrictionHelper.inputs) :
    invoke table factorRestrictionHelper args =
      factorRestrictionBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.factor_restriction_body payload.linked bodies.toRestrictionBodies args

theorem gate_restriction_body (args : Values (assignment F G) gateRestrictionHelper.inputs) :
    invoke table gateRestrictionHelper args =
      gateRestrictionBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gate_restriction_body payload.linked bodies args

theorem gateValuesLeft_body (args : Values (assignment F G) gateValuesLeftHelper.inputs) :
    invoke table gateValuesLeftHelper args =
      gateValuesLeftBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gateValuesLeft_body payload.linked bodies args

theorem gateValuesRight_body (args : Values (assignment F G) gateValuesRightHelper.inputs) :
    invoke table gateValuesRightHelper args =
      gateValuesRightBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gateValuesRight_body payload.linked bodies args

theorem gateValueCallback_body (args : Values (assignment F G) gateValueCallbackHelper.inputs) :
    invoke table gateValueCallbackHelper args =
      gateValueCallbackBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gateValueCallback_body payload.linked bodies args

theorem gateValueRealization_body (args : Values (assignment F G) gateValueRealizationHelper.inputs) :
    invoke table gateValueRealizationHelper args =
      gateValueRealizationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gateValueRealization_body payload.linked bodies args

theorem gateQuadraticCallback_body (args : Values (assignment F G) gateQuadraticCallbackHelper.inputs) :
    invoke table gateQuadraticCallbackHelper args =
      gateQuadraticCallbackBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gateQuadraticCallback_body payload.linked bodies args

theorem gateQuadraticRealization_body (args : Values (assignment F G) gateQuadraticRealizationHelper.inputs) :
    invoke table gateQuadraticRealizationHelper args =
      gateQuadraticRealizationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.gateQuadraticRealization_body payload.linked bodies args

theorem interpolationCallback_body (args : Values (assignment F G) interpolationCallbackHelper.inputs) :
    invoke table interpolationCallbackHelper args =
      interpolationCallbackBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.interpolationCallback_body payload.linked bodies.toRestrictionBodies args

theorem interpolationRealization_body (args : Values (assignment F G) interpolationRealizationHelper.inputs) :
    invoke table interpolationRealizationHelper args =
      interpolationRealizationBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.interpolationRealization_body payload.linked bodies.toRestrictionBodies args

theorem value (a m l r : F) :
    invoke (table (G := G)) gateValueHelper (.cons a (.cons m (.cons l (.cons r .nil)))) =
      .done (.cons (Gate.value a m l r) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.value payload.linked bodies a m l r

theorem quadratic (a0 a1 m0 m1 l0 l1 r0 r1 : F) :
    invoke (table (G := G)) gateQuadraticHelper
      (.cons a0 (.cons a1 (.cons m0 (.cons m1 (.cons l0 (.cons l1 (.cons r0 (.cons r1 .nil)))))))) =
      .done (.cons (Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.quadratic payload.linked bodies a0 a1 m0 m1 l0 l1 r0 r1

theorem linear (a b q : F) :
    invoke (table (G := G)) linearWrapperHelper (.cons a (.cons b (.cons q .nil))) =
      .done (.cons (b - a - q) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.linear payload.linked bodies a b q

theorem interpolate (a b r : F) :
    invoke (table (G := G)) interpolationHelper (.cons a (.cons b (.cons r .nil))) =
      .done (.cons (a + (b - a) * r) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.interpolate payload.linked bodies.toRestrictionBodies a b r

theorem values_callback (x0 x1 x2 x3 : F) (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValueCallbackHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))))))) =
      .done (.cons (Gate.value x0 x1 x2 x3) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.values_callback payload.linked bodies x0 x1 x2 x3 v0 v1 v2 v3

theorem collect_values (v0 v1 v2 v3 : List F) :
    Evaluation.denoteCollect (table (G := G)) gateValuesLeftCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.collect_values payload.linked bodies v0 v1 v2 v3

theorem map_values_left (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValuesLeftHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.map_values_left payload.linked bodies v0 v1 v2 v3

theorem map_values_right (v0 v1 v2 v3 : List F) :
    invoke (table (G := G)) gateValuesRightHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length]) (valuesFormula (F := F) v0 v1 v2 v3) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.map_values_right payload.linked bodies v0 v1 v2 v3

theorem quadratics_callback (x0 x1 x2 x3 x4 x5 x6 x7 : F) (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G)) gateQuadraticCallbackHelper (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))))))))))) =
      .done (.cons (Gate.quadratic x0 x1 x2 x3 x4 x5 x6 x7) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.quadratics_callback payload.linked bodies x0 x1 x2 x3 x4 x5 x6 x7 v0 v1 v2 v3 v4 v5 v6 v7

theorem collect_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    Evaluation.denoteCollect (table (G := G)) gateQuadraticsCollection (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.collect_quadratics payload.linked bodies v0 v1 v2 v3 v4 v5 v6 v7

theorem map_quadratics (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    invoke (table (G := G)) gateQuadraticsHelper (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      mapped (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length]) (quadraticsFormula (F := F) v0 v1 v2 v3 v4 v5 v6 v7) :=
  ZkcSecurity.Bindings.Gkr.RoundsHelperInstallation.map_quadratics payload.linked bodies v0 v1 v2 v3 v4 v5 v6 v7

end
end ZkcSecurity.Examples.Components.GkrRoundsHelpers
