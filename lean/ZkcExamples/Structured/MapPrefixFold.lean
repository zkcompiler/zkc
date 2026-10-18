module

public import ZkcExamples.Structured.MapPrefixTable
public import ZkcExamples.Structured.MapPrefixLaws

@[expose] public section

/-! The retained Prefix closure, including its private finite callback and
unchanged captured point, is linked through the complete checked Payload. -/
namespace ZkcExamples.Structured.MapPrefixFold
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixLaws
open MapPrefixBodies MapPrefixViews MapPrefixTable
open Zkc.Polynomial.Multilinear (restrictPrefixValues)
set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem step_equation (xs : List F) (dimension columns : Nat) (r : F) :
    invoke (program.payload.meanings F G) stepHelper (firstInputs xs dimension columns r) =
      invoke (program.payload.meanings F G) firstHelper (firstInputs xs dimension columns r) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload stepDefinition step_member
    stepBody step_exact (firstInputs xs dimension columns r)).trans
      (step_body _ xs dimension columns r)

theorem foldStep_equation (xs : List F) (dimension columns : Nat) (r : F) (point : List F) :
    invoke (program.payload.meanings F G) foldStepHelper
      (.cons xs (.cons dimension (.cons columns (.cons r (.cons point .nil))))) =
      invoke (program.payload.meanings F G) firstHelper (firstInputs xs dimension columns r) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload foldStepDefinition foldStep_member
    foldStepBody foldStep_exact (.cons xs (.cons dimension (.cons columns (.cons r (.cons point .nil)))))).trans
      ((foldStep_body _ xs dimension columns r point).trans (step_equation xs dimension columns r))

theorem fold_equation (xs : List F) (dimension columns : Nat) (point : List F) :
    invoke (program.payload.meanings F G) foldHelper
      (.cons point (.cons xs (.cons dimension (.cons columns .nil)))) =
      Evaluation.denoteFold (program.payload.meanings F G) foldSpec
        (.cons point (.cons xs (.cons dimension (.cons columns .nil)))) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload foldDefinition fold_member
    foldBody fold_exact (.cons point (.cons xs (.cons dimension (.cons columns .nil))))).trans
      (fold_body _ xs dimension columns point)

theorem foldWrapper_equation (xs : List F) (dimension columns : Nat) (point : List F) :
    invoke (program.payload.meanings F G) foldWrapperHelper (prefixInputs xs dimension columns point) =
      Evaluation.denoteFold (program.payload.meanings F G) foldSpec
        (.cons point (.cons xs (.cons dimension (.cons columns .nil)))) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload foldWrapperDefinition foldWrapper_member
    foldWrapperBody foldWrapper_exact (prefixInputs xs dimension columns point)).trans
      ((foldWrapper_body _ xs dimension columns point).trans (fold_equation xs dimension columns point))

/-- Every reached finite callback uses the same full captured domain vector. -/
theorem transition_equation (point : List F)
    (state : Values (assignment F G) [vector, .index, .index]) (r : F) :
    Evaluation.foldTransition (program.payload.meanings F G) foldSpec (.cons point .nil) .nil state r =
      invoke (program.payload.meanings F G) firstHelper (state.append (.cons r .nil)) := by
  cases state with | cons xs rest => cases rest with | cons dimension rest => cases rest with
    | cons columns rest =>
      cases rest
      change invoke (program.payload.meanings F G) foldStepHelper
        (.cons xs (.cons dimension (.cons columns (.cons r (.cons point .nil))))) = _
      exact foldStep_equation xs dimension columns r point

/-- Finite admission precedes the fold; accepted points compose in list order. -/
theorem prefix_equation (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    invoke (program.payload.meanings F G) prefixHelper (prefixInputs xs dimension columns point) =
      if point.length ≤ dimension then
        .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
      else .halt .reject := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload prefixDefinition prefix_member
    prefixBody prefix_exact (prefixInputs xs dimension columns point)).trans ?_
  refine (prefix_body _ xs dimension columns point).trans ?_
  refine (foldWrapper_equation (G := G) xs dimension columns point).trans ?_
  change Evaluation.denoteFold (program.payload.meanings F G) foldSpec
    ((Values.cons point Values.nil).append ((inputs xs dimension columns).append Values.nil)) = _
  rw [Evaluation.denoteFold_pack]
  have domainAdmitted :
      (foldSpec.domain.denote (.cons point (.nil : Values (assignment F G) []))).admit =
        .returned point := by
    rw [domain_admit, ite_eq_left pointBound]
  simp only [Finite.execute, domainAdmitted, Finite.admitThen]
  have transition : Evaluation.foldTransition (program.payload.meanings F G) foldSpec
      (.cons point .nil) .nil = fun (state : Values (assignment F G) [vector, .index, .index]) r =>
        invoke (program.payload.meanings F G) firstHelper (state.append (.cons r .nil)) := by
    funext state r
    exact transition_equation point state r
  rw [transition]
  exact fold_restriction _ first_equation xs dimension columns point shape lengthBound

/-- The empty point never reaches the positive-dimension guard. -/
theorem prefix_empty (xs : List F) (dimension columns : Nat)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit) :
    invoke (program.payload.meanings F G) prefixHelper (prefixInputs xs dimension columns []) =
      .done (inputs xs dimension columns) := by
  rw [prefix_equation xs dimension columns [] shape lengthBound (by change 0 < indexLimit; decide +kernel)]
  rfl

/-- Too many coordinates reject only through a reached source First callback. -/
theorem prefix_too_long (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) (tooLong : dimension < point.length) :
    invoke (program.payload.meanings F G) prefixHelper (prefixInputs xs dimension columns point) =
      .halt .reject := by
  rw [prefix_equation xs dimension columns point shape lengthBound pointBound,
    ite_eq_right (by omega)]

/-- Logical point-length exhaustion precedes every finite callback. -/
theorem prefix_exhausted (xs : List F) (dimension columns : Nat) (point : List F)
    (invalid : ¬ point.length < indexLimit) :
    invoke (program.payload.meanings F G) prefixHelper (prefixInputs xs dimension columns point) =
      .halt .exhausted := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload prefixDefinition prefix_member
    prefixBody prefix_exact (prefixInputs xs dimension columns point)).trans ?_
  refine (prefix_body _ xs dimension columns point).trans ?_
  refine (foldWrapper_equation (G := G) xs dimension columns point).trans ?_
  change Evaluation.denoteFold (program.payload.meanings F G) foldSpec
    ((Values.cons point Values.nil).append ((inputs xs dimension columns).append Values.nil)) = _
  rw [Evaluation.denoteFold_pack]
  have stopped := domain_admit (G := G) point
  rw [ite_eq_right invalid] at stopped
  simp only [Finite.execute, stopped, Finite.admitThen]

end ZkcExamples.Structured.MapPrefixFold
