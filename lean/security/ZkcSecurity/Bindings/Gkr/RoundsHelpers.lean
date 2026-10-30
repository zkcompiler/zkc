module

public import Zkc.Protocols.Gkr.Source.RoundHelpers
public import Zkc.Protocols.AlgebraicRounds.Gate
public import Zkc.Source.Structured.MapEvaluation
public import Zkc.Source.Structured.CollectionReferenceLaws
public import Zkc.Source.TypedABI
public import ZkcSecurity.Bindings.Gkr.RoundsLayout

@[expose] public section

/-! Reusable GKR helper formulas and complete collection admission, including stops. -/
namespace ZkcSecurity.Examples.Components.GkrRoundsHelpers
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

export ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate
  (emptyHelper emptyBody appendHelper appendBody gateValueHelper gateValueBody gateValuesLeftHelper gateValuesLeftBody gateValuesRightHelper gateValuesRightBody gateValuesLeftCollection gateQuadraticsCollection gateValueCallbackHelper gateValueCallbackBody gateValueRealizationHelper gateValueRealizationBody gateQuadraticCallbackHelper gateQuadraticCallbackBody gateQuadraticRealizationHelper gateQuadraticRealizationBody interpolationCallbackHelper interpolationCallbackBody interpolationRealizationHelper interpolationRealizationBody interpolationsCollection gateQuadraticHelper gateQuadraticBody gateQuadraticsHelper gateQuadraticsBody linearCoefficientHelper linearCoefficientBody linearWrapperHelper linearWrapperBody roundMessageHelper roundMessageBody interpolationHelper interpolationBody interpolationsHelper interpolationsBody factorRestrictionHelper factorRestrictionBody gateRestrictionHelper gateRestrictionBody)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def mapped {I : PIR.Signature} (shape : PIR.Outcome Nat) (formula : Nat → F) :
    PIR.Process I (Values (assignment F G) [.vector "bls12-381.fr"]) :=
  Finite.admitThen shape fun length => .done (.cons ((List.range length).map formula) .nil)

def valuesFormula (v0 v1 v2 v3 : List F) (i : Nat) : F :=
  Gate.value (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Every row's capacity check precedes its zip equality check and the next row. -/
theorem values_domain (v0 v1 v2 v3 : List F) :
    gateValuesLeftCollection.domain.admit (carriers := uniformCarriers F G) (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))) =
      Finite.continueWith (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length])
        (fun n => .returned ((List.range n).map fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) .nil)))))) := by
  simp only [gateValuesLeftCollection, DomainSpec.admit, DomainBody.admit, DomainNode.admit,
    Collection.values, Collection.type, Collection.element, TypedABI.get_cons_there, Values.get, Operands.eval]
  rw [list_map_range v0 0, list_map_range v1 0, list_map_range v2 0, list_map_range v3 0]
  simp only [Evaluation.mapShape, Evaluation.mapShapeRemaining]
  all_goals by_cases small0 : v0.length < indexLimit <;> simp_all only [Finite.continueWith, ↓reduceIte, eq_comm]
  all_goals by_cases small1 : v1.length < indexLimit <;> simp_all only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same1 : v1.length = v0.length <;> simp_all only [↓reduceIte, eq_comm]
  all_goals by_cases small2 : v2.length < indexLimit <;> simp_all only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same2 : v2.length = v0.length <;> simp_all only [↓reduceIte, eq_comm]
  all_goals by_cases small3 : v3.length < indexLimit <;> simp_all only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same3 : v3.length = v0.length <;> simp_all only [↓reduceIte, eq_comm]


def quadraticsFormula (v0 v1 v2 v3 v4 v5 v6 v7 : List F) (i : Nat) : F :=
  Gate.quadratic (v0[i]?.getD 0) (v1[i]?.getD 0) (v2[i]?.getD 0) (v3[i]?.getD 0) (v4[i]?.getD 0) (v5[i]?.getD 0) (v6[i]?.getD 0) (v7[i]?.getD 0)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Every row's capacity check precedes its zip equality check and the next row. -/
theorem quadratics_domain (v0 v1 v2 v3 v4 v5 v6 v7 : List F) :
    gateQuadraticsCollection.domain.admit (carriers := uniformCarriers F G) (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 (.cons v6 (.cons v7 .nil)))))))) =
      Finite.continueWith (Evaluation.mapShape [v0.length, v1.length, v2.length, v3.length, v4.length, v5.length, v6.length, v7.length])
        (fun n => .returned ((List.range n).map fun i => (.cons (v0[i]?.getD 0) (.cons (v1[i]?.getD 0) (.cons (v2[i]?.getD 0) (.cons (v3[i]?.getD 0) (.cons (v4[i]?.getD 0) (.cons (v5[i]?.getD 0) (.cons (v6[i]?.getD 0) (.cons (v7[i]?.getD 0) .nil)))))))))) := by
  simp only [gateQuadraticsCollection, DomainSpec.admit, DomainBody.admit, DomainNode.admit,
    Collection.values, Collection.type, Collection.element, TypedABI.get_cons_there, Values.get, Operands.eval]
  rw [list_map_range v0 0, list_map_range v1 0, list_map_range v2 0, list_map_range v3 0, list_map_range v4 0, list_map_range v5 0, list_map_range v6 0, list_map_range v7 0]
  simp only [Evaluation.mapShape, Evaluation.mapShapeRemaining]
  all_goals by_cases small0 : v0.length < indexLimit <;> simp_all (maxSteps := 1000000) only [Finite.continueWith, ↓reduceIte, eq_comm]
  all_goals by_cases small1 : v1.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same1 : v1.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]
  all_goals by_cases small2 : v2.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same2 : v2.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]
  all_goals by_cases small3 : v3.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same3 : v3.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]
  all_goals by_cases small4 : v4.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same4 : v4.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]
  all_goals by_cases small5 : v5.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same5 : v5.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]
  all_goals by_cases small6 : v6.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same6 : v6.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]
  all_goals by_cases small7 : v7.length < indexLimit <;> simp_all (maxSteps := 1000000) only [zipDomainRows_ranges, Values.append, ↓reduceIte]
  all_goals by_cases same7 : v7.length = v0.length <;> simp_all (maxSteps := 1000000) only [↓reduceIte, eq_comm]

end
end ZkcSecurity.Examples.Components.GkrRoundsHelpers
