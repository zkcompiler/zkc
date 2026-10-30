import Tests.ConnectionTargetPlacementRoots
import Tests.ConnectionTargetPlacementHistory
import Tests.ConnectionContinuationMutation
import Tests.ConnectionRefusal

/-! Refusals distinguish a registered checked family from arbitrary reuse of
an old source/body proof. Resource exhaustion is never a successful control. -/
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
noncomputable section
namespace Tests.ConnectionTargetPlacementControls
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement
open Tests.ConnectionTargetPlacementRoots

def pinnedTemplate : SourceTemplate Tests.ConnectionTargetPlacement.program.payload [] :=
  {Tests.ConnectionTargetPlacement.template with pins := [some 0]}
def pinnedEntry : Entry Tests.ConnectionTargetPlacement.program.payload pinnedTemplate.key :=
  ⟨[], .empty, pinnedTemplate, rfl⟩

-- Pins do not occur in the normalized Alignment type. A closed candidate
-- makes this control independent of interface proof search: ignoring entry
-- identity would accept it immediately for the same alignment goal.
def closedAliasBody : CheckedBody Tests.ConnectionTargetPlacement.entry
    Tests.ConnectionTargetPlacement.routing .unselected
    (Tests.ConnectionTargetPlacement.stepPlacement Tests.ConnectionTargetPlacement.routing aliasContext
      aliasFrames aliasLayout (.var .here) (.var .here) (.var (.there .here)) 3 3 4 true) :=
  ⟨aliased.alignment, Tests.ConnectionTargetPlacement.stepExtent
    Tests.ConnectionTargetPlacement.routing aliasContext 7 3 3 4⟩
attribute [local connection_target_body] closedAliasBody

example : True := by
  run_tac
    let type ← Lean.Meta.inferType (← Lean.Elab.Term.elabTerm (← `(aliased.alignment)) none)
    let goal ← Lean.Meta.mkFreshExprMVar type
    let entry := Lean.mkConst ``pinnedEntry
    let placement ← Lean.Elab.Term.elabTerm (← `(
      Tests.ConnectionTargetPlacement.stepPlacement Tests.ConnectionTargetPlacement.routing aliasContext
        aliasFrames aliasLayout (.var .here) (.var .here) (.var (.there .here)) 3 3 4 true)) none
    let result ← ZkcTools.ConstructionBindings.TargetPlacement.propose goal.mvarId! entry placement
      (fun _ => Lean.throwError "closed control unexpectedly asked for an interface proof")
    unless result.isNone do Lean.throwError "placement matched an entry with different pins"
  trivial

set_option zkc.connection.requireReusableBodies true

example : True := by
  expect_connection_refusal "changed admitted source entry" because "alignment-reusable-body-refused"
    have : ConnectionRoot.RootCertificate Tests.ConnectionContinuationMutation.changedProgram
        Tests.ConnectionContinuationMutation.changedRouting 1 Tests.SourceConnectionPilot.artifact := by
      derive_root_connection_with_library
        target Tests.SourceConnectionPilot.rootView
        correspondence Tests.ConnectionContinuationMutation.changedCorrespondence
        services [] library Tests.ConnectionContinuationMutation.changedLibrary
  trivial

example : True := by
  expect_connection_refusal "missing static occurrence route" because "alignment-reusable-body-refused"
    have : ConnectionRoot.RootCertificate Tests.ConnectionTargetPlacement.program
        {rootRouting with messages := []} 1 Tests.SourceConnectionPilot.artifact := by
      derive_root_connection_with_library
        target Tests.SourceConnectionPilot.rootView
        correspondence Tests.SourceConnectionPilot.body_view
        services [] library library
  trivial

-- Omitting the only returned component cannot factor through this caller.
example : ConnectionReturnProjection.continuation
    (.cons false .nil : ConnectionReturnProjection.Selection [.index])
    (.done (.cons (.read .here .here) .nil) : Form [] [] [.tuple [.index]] [.index]) ≠
    .done (.cons (.read .here .here) .nil) := by
  intro same
  have different : true = false := congrArg (fun value : Form [] [] [.tuple [.index]] [.index] =>
    match value with | .done (.cons .absent .nil) => true | _ => false) same
  cases different

-- Extents, frame custody and nominal read types remain ordinary typed checks.
example : ¬ applicationAdmitted 7 6 [] none := by decide +kernel
example : ¬ applicationAdmitted 7 7 [.data 7] none := by decide +kernel
example : ¬ applicationAdmitted 7 8 [.data 7] (some 7) := by decide +kernel
example : True := by
  expect_connection_refusal "nominal Boolean read from index cell" because "Application type mismatch"
    have : Readback ([.data (.present (.index 1))] : Layout [])
        (.cons (.present (.bool true)) .nil) [.data 0] := .data 0 rfl .nil
  trivial
example : True := by
  expect_connection_refusal "stale retained history" because "Application type mismatch"
    have : HistoryReadback ([.unused, .history "suite"] : Layout []) "suite" (some 0) :=
      .transcript 0 rfl
  trivial
example : True := by
  expect_connection_refusal "changed nominal history suite" because "Application type mismatch"
    have : HistoryReadback ([.history "other"] : Layout []) "suite" (some 0) :=
      .transcript 0 rfl
  trivial
end Tests.ConnectionTargetPlacementControls
