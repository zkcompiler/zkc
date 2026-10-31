import Tests.ConnectionTargetPlacement
import Tests.ConnectionTargetPlacementRoots
import Tests.ConnectionTargetPlacementHistory
import Tests.ConnectionRefusal
import Tests.ConnectionPlacementMetrics

/-! A family installed from its symbolic interface, with no authored body
derivation. The input readbacks and occurrence route are finite premises; the
guard, stopping helper, all-reply receive, full return and extent are generated
once by the ordinary typed proposer. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
noncomputable section
namespace Tests.ConnectionTargetPlacementInstallation
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement
open Tests.ConnectionTargetPlacement
open Tests.ConnectionTargetPlacementRoots (aliasScope aliasLayout aliasFrames aliasContext)

attribute [-connection_target_body] checkedStep
attribute [-connection_target_body] checkedOptionalPresentStep

install_connection_target_body installedStep {scope : Scope}
    (routing : Original.Routing) (plain : routing.context.profile = .plain)
    (selection : Selection program.payload.definitions entry.earlierKeys)
    (context : ProtocolContext) (frames : ScopedFrames scope) (layout : Layout scope)
    (guard helper : Term [] scope .boolean) (seed : Term [] scope .index)
    (guardRef helperRef seedRef : Nat) (keep : Bool)
    (guardRead : GuardReadback layout .boolean guard (.bool true) guardRef)
    (helperRead : Readback guardRead.refine (.cons (.present helper) (.cons (.present seed) .nil))
      [.data helperRef, .data seedRef])
    (message : Template)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message (qualifyProtocolSite context.applicationPrefix "message")
        (context.roles 0) routing.self) (frames.rename (target := .tuple [.index] :: scope) .there).sites
      routing.messages = some message) :
    CheckedBody entry routing selection
      (stepPlacement routing context frames layout guard helper seed guardRef helperRef seedRef keep)

install_connection_target_body installedOptionalStep {scope : Scope}
    (routing : Original.Routing) (plain : routing.context.profile = .plain)
    (selection : Selection program.payload.definitions optionalEntry.earlierKeys)
    (context : ProtocolContext) (frames : ScopedFrames scope) (layout : Layout scope)
    (guard : Term [] scope .boolean) (helper : Comp [] scope .boolean) (seed : Comp [] scope .index)
    (guardRef helperRef seedRef : Nat) (keep : Bool)
    (guardRead : GuardReadback layout .boolean guard (.bool true) guardRef)
    (helperRead : Readback guardRead.refine
      (.cons (ConnectionSubstitution.component (ConnectionSubstitution.valueHead guard) (helper.rename .there))
        (.cons (ConnectionSubstitution.component (ConnectionSubstitution.valueHead guard) (seed.rename .there)) .nil))
      [.data helperRef, .data seedRef])
    (message : Template)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message (qualifyProtocolSite context.applicationPrefix "message")
        (context.roles 0) routing.self) (frames.rename (target := .tuple [.index] :: scope) .there).sites
      routing.messages = some message) :
    CheckedBody optionalEntry routing selection
      (optionalPresentPlacement routing context frames layout guard helper seed guardRef helperRef seedRef keep)

def library : Bundle program.payload := ⟨[template.key], .extend .empty template⟩

def callee : Fin [template.key].length := ⟨0, by decide +kernel⟩

/-- Consecutive applications consume the preceding full return, so every
callee return remains live. Runtime repeats are not unrolled by this fixture. -/
def calls {scope : Scope} (count : Nat) (guard helper : Term [] scope .boolean)
    (seed : Term [] scope .index) : Form [] [template.key] scope [.index] :=
  match count with
  | 0 => .done (.cons (.present seed) .nil)
  | count + 1 => .apply callee template.key.signature [0,1] "first"
      (.cons guard (.cons helper (.cons seed .nil)) : Values (Argument [] scope) template.pattern.scope)
      (.split (.read .here .here) (.halt .incomplete)
        (calls count ((guard.rename .there).rename .there) ((helper.rename .there).rename .there)
          (.var .here)))

def target (count size seedRef : Nat) : ConnectionCertificate.Block :=
  match count with
  | 0 => fun _ => Domain.View.empty
  | count + 1 => (stepSpine routing aliasContext 3 3 seedRef).plug
      (target count (size + 2) (size + 1))

def Applications (count : Nat) :=
  Alignment routing {} program.payload.definitions library.keys
    (selection := .selected program.payload rfl library.library) [.index] 1 [[0,1]]
    [.data (7 + 2 * count - 1)] none aliasFrames aliasLayout
    (calls count (.var .here) (.var .here) (.var (.there .here)))
    (target count 7 4)

set_option zkc.connection.requireReusableBodies true

measured_placement_decl one : Applications 1 := by derive_connection_alignment
measured_placement_decl two : Applications 2 := by derive_connection_alignment
measured_placement_decl four : Applications 4 := by derive_connection_alignment
measured_placement_decl eight : Applications 8 := by derive_connection_alignment

audit_placements one 1 [installedStep]
audit_placements two 2 [installedStep]
audit_placements four 4 [installedStep]
audit_placements eight 8 [installedStep]

-- Reassemble an actual admitted root, including its independent reached-route
-- judgment and complete outputs. Both symbolic repeat indices remain live.
measured_placement_decl nested : ConnectionRoot.RootCertificate program
    Tests.ConnectionTargetPlacementRoots.rootRouting 1 Tests.SourceConnectionPilot.artifact := by
  derive_root_connection_with_library
    target Tests.SourceConnectionPilot.rootView
    correspondence Tests.SourceConnectionPilot.body_view
    services [] library Tests.ConnectionTargetPlacementRoots.library

audit_placements nested 2 [installedOptionalStep]

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  nested.simulation model physical

def nestedFacts := nested.facts
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  nestedFacts.coverage model physical

example : True := by
  expect_connection_refusal "same-type seed and enclosing coordinate swapped" because "alignment-reusable-body-refused"
    have : Alignment routing {} program.payload.definitions library.keys
        (selection := .selected program.payload rfl library.library) [.index] 1 [[0,1]]
        [.data 8] none aliasFrames aliasLayout
        (calls 1 (.var .here) (.var .here) (.var (.there .here)))
        (stepSpine routing aliasContext 3 3 5).block := by
      derive_connection_alignment
  trivial

def pinnedTemplate : SourceTemplate program.payload [] := {template with pins := [some 0]}
def pinnedEntry : Entry program.payload pinnedTemplate.key := ⟨[], .empty, pinnedTemplate, rfl⟩

example : True := by
  run_tac
    let placement ← Lean.Elab.Term.elabTerm (← `(
      stepPlacement routing aliasContext aliasFrames aliasLayout
        (.var .here) (.var .here) (.var (.there .here)) 3 3 4 true)) none
    let type ← Lean.Elab.Term.elabType (← `(
      Alignment routing aliasContext program.payload.definitions []
        (selection := .unselected) [.index] 1 [[0,1]] [.data 8] none aliasFrames aliasLayout
        (ConnectionReturnProjection.form (.cons true .nil)
          (ConnectionSubstitution.form entry.form (fun binder => entryAt
            (stepPlacement routing aliasContext aliasFrames aliasLayout
              (.var .here) (.var .here) (.var (.there .here)) 3 3 4 true).arguments binder)))
        (stepSpine routing aliasContext 3 3 4).block))
    let goal ← Lean.Meta.mkFreshExprMVar type
    let found ← ZkcTools.ConstructionBindings.TargetPlacement.propose goal.mvarId!
      (Lean.mkConst ``pinnedEntry) placement
      (fun _ => Lean.throwError "pins control unexpectedly requested an interface proof")
    unless found.isNone do Lean.throwError "installed family accepted changed Entry pins"
  trivial

#print axioms installedStep
#print axioms installedOptionalStep
#print axioms eight
#print axioms nestedFacts
end Tests.ConnectionTargetPlacementInstallation

namespace Tests.ConnectionTargetPlacementInstallation.Retained
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement
open Tests.ConnectionRetainedHistory (validatorRouting artifact target target_eq)

attribute [-connection_target_body] Tests.ConnectionTargetPlacementHistory.checkedKeep

install_connection_target_body installedKeep {scope : Scope} (routing : Original.Routing)
    (selection : Selection Tests.ConnectionRetainedHistory.program.payload.definitions
      Tests.ConnectionTargetPlacementHistory.entry.earlierKeys)
    (context : ProtocolContext) (frames : ScopedFrames scope) (layout : Layout scope)
    (input : Comp [] scope .boolean) (output : Original.Location) (history : Option Nat) (keep : Bool)
    (read : Readback layout (.cons (if keep then input else .absent) .nil) [output])
    (current : HistoryReadback layout routing.context.suite history) :
    CheckedBody Tests.ConnectionTargetPlacementHistory.entry routing selection
      (Tests.ConnectionTargetPlacementHistory.placement context frames layout input output history keep)

set_option zkc.connection.requireReusableBodies true in
measured_placement_decl retained : ConnectionRoot.RootCertificate
    Tests.ConnectionRetainedHistory.program validatorRouting 1 artifact := by
  derive_root_connection_with_library target Tests.ConnectionRetainedHistory.target correspondence target_eq
    services [] library Tests.ConnectionTargetPlacementHistory.library

audit_placements retained 1 [installedKeep]
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  retained.simulation model physical

#print axioms installedKeep
#print axioms retained
end Tests.ConnectionTargetPlacementInstallation.Retained
