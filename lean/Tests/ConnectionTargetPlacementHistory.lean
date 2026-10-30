import Tests.ConnectionRetainedHistory
import Tests.ConnectionPlacementMetrics
import Zkc.Construction.ConnectionTargetPlacement

/-! A different admitted callee, exact full return, and retained current
history use the same reusable placement path as fresh-history applications. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace Tests.ConnectionTargetPlacementHistory
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement
open Tests.ConnectionRetainedHistory (program validatorRouting artifact target target_eq)

def template : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 (.cons .optional .nil)).toOption.get (by decide +kernel)
def entry : Entry program.payload template.key := ⟨[], .empty, template, rfl⟩
def library : Bundle program.payload := ⟨[template.key], .extend .empty template⟩

def placement {scope : Scope} (context : ProtocolContext) (frames : ScopedFrames scope)
    (layout : Layout scope) (input : Comp [] scope .boolean) (output : Original.Location)
    (history : Option Nat) (keep : Bool) : Placement template.key where
  context := context
  scope := scope
  arguments := .cons input .nil
  frames := frames
  layout := layout
  outputs := [output]
  history := history
  returns := .cons keep .nil
  spine := .empty
  extent := layout.length

@[connection_target_body] def checkedKeep {scope : Scope} (routing : Original.Routing)
    (selection : Selection program.payload.definitions entry.earlierKeys)
    (context : ProtocolContext) (frames : ScopedFrames scope) (layout : Layout scope)
    (input : Comp [] scope .boolean) (output : Original.Location) (history : Option Nat) (keep : Bool)
    (read : Readback layout (.cons (if keep then input else .absent) .nil) [output])
    (current : HistoryReadback layout routing.context.suite history) :
    CheckedBody entry routing selection (placement context frames layout input output history keep) where
  alignment := .done (by cases keep <;> exact read) current
  physicalExtent := .empty layout.length

set_option zkc.connection.requireReusableBodies true in
measured_placement_decl validator : ConnectionRoot.RootCertificate program validatorRouting 1 artifact := by
  derive_root_connection_with_library target target correspondence target_eq services [] library library

audit_placements validator 1 [checkedKeep]
example (model : DomainModel) (environment : Domain.Environment model.toCarriers) :=
  validator.simulation model environment

-- The family cannot replace current-history, route, or complete-return checks.
set_option zkc.connection.requireReusableBodies true in
example : True := by
  fail_if_success
    have : ConnectionRoot.RootCertificate program validatorRouting 1 {artifact with returned := [0,0]} := by
      derive_root_connection_with_library target target correspondence target_eq services [] library library
  trivial

#print axioms validator
end Tests.ConnectionTargetPlacementHistory
