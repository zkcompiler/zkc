module

public import ZkcExamples.Structured.OriginalSumcheckCalls
public import ZkcExamples.Structured.NormalFormSteps

@[expose] public section

/-! Installed source mathematics shared by generated producer assemblies.
Root layout, source names and artifact positions are not parameters of these laws. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.OriginalSumcheckProducerCalls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open OriginalSumcheckLibrary SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev realizeProducerCall (payload : UnitPayload) (maximum : Nat) (context : ProtocolContext)
    (outputs : List (List Nat))
    (inputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceInputs) :=
  (OriginalSumcheckLibrary.reduce payload maximum context (context.roles 0) []
    (maskValues (context.roles 0) (context.mapScopes [[0], [0], [0], [1], [0, 1], [1]]) inputs)).bind
    (fun result => .done (maskValues (context.roles 0) (context.mapScopes outputs) result))

theorem table_lift (payload : UnitPayload)
    (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (raw : List F) (count : Nat) (shape : PrimitiveLibrary.HasShape raw count 1)
    (bounded : raw.length < indexLimit) :
    invoke (helpers (F := F) (G := G) payload).closed MapFirstBodies.tableHelper
      (PrimitiveLibrary.inputs raw count 1) = .done (PrimitiveLibrary.inputs raw count 1) := by
  rw [← (helpers_lift payload).closed, closed_invoke_plain,
    MapFirstContracts.table_equation payload.linked bodies.first raw count 1 bounded
      (lt_trans shape.2.1 (by decide +kernel)) (by decide +kernel), ite_eq_left shape]
  rfl

theorem table_owned (payload : UnitPayload)
    (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (raw : List F) (count : Nat) (shape : PrimitiveLibrary.HasShape raw count 1)
    (bounded : raw.length < indexLimit) :
    Participant.owned 0 0
      (invoke (helpers (F := F) (G := G) payload).closed MapFirstBodies.tableHelper)
      (.cons (some raw) (.cons (some count) (.cons (some 1) .nil))) =
      .done (.cons (some raw) (.cons (some count) (.cons (some 1) .nil))) :=
  NormalFormSteps.owned_done 0 (PrimitiveLibrary.inputs raw count 1)
    (table_lift payload bodies raw count shape bounded)

end ZkcExamples.Structured.OriginalSumcheckProducerCalls
