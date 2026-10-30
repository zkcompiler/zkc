import Tests.ConnectionSharedLibrary
import Zkc.Construction.ConnectionTargetPlacement
import ZkcTools.ConstructionBindings.Alignment

/-! A checked family relocates a guard, stopping owned helper and all-reply
receive across arbitrary caller scopes, read references and fresh SSA offsets.
Only readbacks and occurrence routing are supplied at a use. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace Tests.ConnectionTargetPlacement
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement

abbrev program := Tests.SourceConnectionPilot.program
abbrev routing := Tests.SourceConnectionPilot.routing
abbrev template := Tests.ConnectionSharedLibrary.template

def entry : Entry program.payload template.key := ⟨[], .empty, template, rfl⟩

def stepSpine (routing : Original.Routing) (context : ProtocolContext) (guardRef helperRef seedRef : Nat) : ConnectionTargetPrefix.Prefix :=
  .step (fun _ => Domain.View.guard guardRef []) <|
  .step (fun model => Domain.View.helper model program "gate" [helperRef, seedRef] [.data .index]) <|
  .step (fun _ => Domain.View.receive (qualifyProtocolSite context.applicationPrefix "message")
    (qualifyProtocolSite context.applicationPrefix "message") (routing.context.role (context.roles 0))
    .index [.data .index]) .empty

def stepExtent (routing : Original.Routing) (context : ProtocolContext)
    (size guardRef helperRef seedRef : Nat) :
    ConnectionTargetExtent.Extent size (size + 2) (stepSpine routing context guardRef helperRef seedRef).block := by
  exact .sequence (.guard size guardRef [])
    (.sequence (.helper size program "gate" [helperRef, seedRef] [.data .index])
      (.sequence (.receive (size + 1)
        (qualifyProtocolSite context.applicationPrefix "message")
        (qualifyProtocolSite context.applicationPrefix "message")
        (routing.context.role (context.roles 0)) .index [.data .index])
        (.empty (size + 2))))

def stepPlacement {scope : Scope} (routing : Original.Routing) (context : ProtocolContext) (frames : ScopedFrames scope)
    (layout : Layout scope) (guard helper : Term [] scope .boolean) (seed : Term [] scope .index)
    (guardRef helperRef seedRef : Nat) (keep : Bool) : Placement template.key where
  context := context
  scope := scope
  arguments := .cons guard (.cons helper (.cons seed .nil))
  frames := frames
  layout := layout
  outputs := [if keep then .data (layout.length + 1) else .absent]
  history := none
  returns := .cons keep .nil
  spine := stepSpine routing context guardRef helperRef seedRef
  extent := layout.length + 2

/-- One body derivation serves all admitted placements. Its physical inputs may alias whenever
the typed readbacks hold. Every write appends beyond the whole caller layout.
The occurrence route and dynamic frame stack are independently checked. -/
@[connection_target_body] def checkedStep {scope : Scope}
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
      (stepPlacement routing context frames layout guard helper seed guardRef helperRef seedRef keep) where
  alignment := by
    apply Alignment.guard .boolean guard (.bool true) guardRef guardRead
    apply Alignment.ownedHelper 1 program Tests.SourceConnectionPilot.gateHelper
      ⟨⟨0, by decide⟩, rfl, rfl⟩ _ [helperRef, seedRef] rfl rfl helperRead
    apply Alignment.receive .index "message" 0 plain message route rfl
    cases keep
    · exact .done (.absent .nil) .plain
    · exact Alignment.done (Readback.data (layout.length + 1) (by
        change (receiveLayout (ConnectionComputation.tupleLayout guardRead.refine [.index]) .index)[layout.length + 1]? =
          some (.data (.present (.var .here)))
        have size : (ConnectionComputation.tupleLayout guardRead.refine [.index]).length =
            layout.length + 1 := by
          simp [ConnectionComputation.tupleLayout, ConnectionComputation.cells, readComps,
            Operands.identity, Operands.rename, mapValues, GuardReadback.refine]
        rw [receiveLayout, ← size]
        simp) .nil) .plain
  physicalExtent := stepExtent routing context layout.length guardRef helperRef seedRef

def optionalPattern : InputPattern Tests.SourceConnectionPilot.stepInputs :=
  .cons .optional (.cons .optional (.cons .optional .nil))
def optionalTemplate : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 optionalPattern).toOption.get (by decide +kernel)
def optionalEntry : Entry program.payload optionalTemplate.key := ⟨[], .empty, optionalTemplate, rfl⟩

def optionalPresentPlacement {scope : Scope} (routing : Original.Routing) (context : ProtocolContext)
    (frames : ScopedFrames scope) (layout : Layout scope) (guard : Term [] scope .boolean)
    (helper : Comp [] scope .boolean) (seed : Comp [] scope .index)
    (guardRef helperRef seedRef : Nat) (keep : Bool) : Placement optionalTemplate.key where
  context := context
  scope := scope
  arguments := .cons (.present guard) (.cons helper (.cons seed .nil))
  frames := frames
  layout := layout
  outputs := [if keep then .data (layout.length + 1) else .absent]
  history := none
  returns := .cons keep .nil
  spine := stepSpine routing context guardRef helperRef seedRef
  extent := layout.length + 2

/-- Optional source inputs also admit a known-present guard at an actual call. -/
@[connection_target_body] def checkedOptionalPresentStep {scope : Scope}
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
      (optionalPresentPlacement routing context frames layout guard helper seed guardRef helperRef seedRef keep) where
  alignment := by
    apply Alignment.splitValue guard rfl
    apply Alignment.guard .boolean guard (.bool true) guardRef guardRead
    apply Alignment.ownedHelper 1 program Tests.SourceConnectionPilot.gateHelper
      ⟨⟨0, by decide⟩, rfl, rfl⟩ _ [helperRef, seedRef] rfl rfl helperRead
    apply Alignment.receive .index "message" 0 plain message route rfl
    cases keep
    · exact .done (.absent .nil) .plain
    · exact Alignment.done (Readback.data (layout.length + 1) (by
        change (receiveLayout (ConnectionComputation.tupleLayout guardRead.refine [.index]) .index)[layout.length + 1]? =
          some (.data (.present (.var .here)))
        have size : (ConnectionComputation.tupleLayout guardRead.refine [.index]).length =
            layout.length + 1 := by
          simp [ConnectionComputation.tupleLayout, ConnectionComputation.cells, readComps,
            Operands.identity, Operands.rename, mapValues, GuardReadback.refine]
        rw [receiveLayout, ← size]
        simp) .nil) .plain
  physicalExtent := stepExtent routing context layout.length guardRef helperRef seedRef

def optionalPlacement {scope : Scope} (routing : Original.Routing) (context : ProtocolContext)
    (frames : ScopedFrames scope) (layout : Layout scope) (guard : Var scope (.component .boolean))
    (helper : Comp [] scope .boolean) (seed : Comp [] scope .index)
    (guardRef helperRef seedRef : Nat) (keep : Bool) : Placement optionalTemplate.key where
  context := context
  scope := scope
  arguments := .cons (.input guard) (.cons helper (.cons seed .nil))
  frames := frames
  layout := layout
  outputs := [if keep then .data (layout.length + 1) else .absent]
  history := none
  returns := .cons keep .nil
  spine := stepSpine routing context guardRef helperRef seedRef
  extent := layout.length + 2

def presentGuard {scope : Scope} {layout : Layout scope} (guard : Var scope (.component .boolean))
    (reference : Nat) (read : layout[reference]? = some (.data (.input guard))) :
    GuardReadback (layout.map (Cell.presentAt (.input guard))) .boolean (.var .here) (.bool true) reference :=
  .boolean _ reference (.data reference (by
    simp [List.getElem?_map, read, Cell.presentAt, Comp.presentAt, Subject.same?, Var.same?, Var.hereAs]) .nil)

/-- The ordinary role-pattern library has optional inputs. Physical readback
discharges the guard's presence split without assuming successful source
execution. Hidden/absent helper inputs still use the original component laws. -/
@[connection_target_body] def checkedOptionalStep {scope : Scope}
    (routing : Original.Routing) (plain : routing.context.profile = .plain)
    (selection : Selection program.payload.definitions optionalEntry.earlierKeys)
    (context : ProtocolContext) (frames : ScopedFrames scope) (layout : Layout scope)
    (guard : Var scope (.component .boolean))
    (helper : Comp [] scope .boolean) (seed : Comp [] scope .index)
    (guardRef helperRef seedRef : Nat) (keep : Bool)
    (guardCell : layout[guardRef]? = some (.data (.input guard)))
    (helperRead : Readback (presentGuard guard guardRef guardCell).refine
      (.cons (helper.rename .there) (.cons (seed.rename .there) .nil)) [.data helperRef, .data seedRef])
    (message : Template)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message (qualifyProtocolSite context.applicationPrefix "message")
        (context.roles 0) routing.self)
      ((frames.rename (target := .value .boolean :: scope) .there).rename
        (target := .tuple [.index] :: .value .boolean :: scope) .there).sites routing.messages = some message) :
    CheckedBody optionalEntry routing selection
      (optionalPlacement routing context frames layout guard helper seed guardRef helperRef seedRef keep) where
  alignment := by
    apply Alignment.splitPresent (.input guard) guardRef guardCell rfl
    apply Alignment.guard .boolean (.var .here) (.bool true) guardRef (presentGuard guard guardRef guardCell)
    apply Alignment.ownedHelper 1 program Tests.SourceConnectionPilot.gateHelper
      ⟨⟨0, by decide⟩, rfl, rfl⟩ _ [helperRef, seedRef] rfl rfl helperRead
    apply Alignment.receive .index "message" 0 plain message route rfl
    cases keep
    · exact .done (.absent .nil) .plain
    · exact Alignment.done (Readback.data (layout.length + 1) (by
        change (receiveLayout
          (ConnectionComputation.tupleLayout (presentGuard guard guardRef guardCell).refine [.index])
          .index)[layout.length + 1]? = some (.data (.present (.var .here)))
        have size : (ConnectionComputation.tupleLayout
            (presentGuard guard guardRef guardCell).refine [.index]).length = layout.length + 1 := by
          simp [ConnectionComputation.tupleLayout, ConnectionComputation.cells, readComps,
            Operands.identity, Operands.rename, mapValues, GuardReadback.refine]
        rw [receiveLayout, ← size]
        simp) .nil) .plain
  physicalExtent := stepExtent routing context layout.length guardRef helperRef seedRef

#print axioms checkedStep
#print axioms checkedOptionalPresentStep
#print axioms checkedOptionalStep
#print axioms CheckedBody.place
#print axioms CheckedBody.prependCalculation
end Tests.ConnectionTargetPlacement
