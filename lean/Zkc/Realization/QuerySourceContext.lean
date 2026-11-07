module

public import Zkc.Realization.QuerySavedSource

@[expose] public section

/-! Fix the saved parent's child operations to its actual source installation.
The older registry is recovered from source reachability, rather than selected
by a companion. Completed or stopped body execution then reconnects to the
original query, including its query charge and leading source event.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Realization.QuerySavedSource
open Zkc.Source Zkc.Source.Structured

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {checked : CheckedOracle snapshot domains math}
  {layout : VirtualStorage.Layout checked.declaration.inputs.dropLast}
  {references : CaptureLayout.References} {entries : OracleEntries model snapshot domains math}
  {records : List (model.Value layout.recordType)} {frame : QueryContinuation.Frame}

structure SourceContext (parent : Parent layout references entries records frame)
    (owner : Nat) where
  older : OracleEntries model snapshot domains math
  located : OracleStore.Located entries
    (VirtualStorage.table checked parent.location parent.rows parent.holder
      parent.receivers parent.captures) older
  reachable : OracleStore.Reachable owner older
  smaller : older.length < entries.length

/-- Actual source reachability and the installed parent determine a valid
older registry. Its body and captures are already fixed by `Parent`. -/
theorem Parent.sourceContext (parent : Parent layout references entries records frame)
    {self : Nat} (reachable : OracleStore.Reachable self entries) :
    Nonempty (SourceContext parent self) := by
  obtain ⟨older, located, earlier, _, smaller⟩ := parent.installed.source_context reachable
  exact ⟨⟨older, located, earlier, smaller⟩⟩

def Parent.request (parent : Parent layout references entries records frame)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation)) : OracleRead :=
  ⟨checked.declaration.kind, parent.location.anchor, frame.position, site, expansion⟩

variable {parent : Parent layout references entries records frame} {self : Nat} {S E : Type}

/-- A saved-answer update retains the original installation context. It
cannot select a newer registry when the next sibling is entered. -/
def SourceContext.withAnswers (context : SourceContext parent self) (answers : List Nat) :
    SourceContext (parent.withAnswers answers) self :=
  ⟨context.older, context.located, context.reachable, context.smaller⟩

/-- Later fresh constructions cannot change the registry used by an already
saved parent's children. The same context survives physical store growth. -/
def SourceContext.transport (context : SourceContext parent self)
    {newReferences : CaptureLayout.References}
    {newEntries : OracleEntries model snapshot domains math}
    {newRecords : List (model.Value layout.recordType)}
    (registry : OracleStore.FreshExtension entries newEntries) (physical : records <+: newRecords)
    (kept : ∀ kind identity anchor reference,
      references kind identity anchor reference → newReferences kind identity anchor reference) :
    SourceContext (parent.transport registry physical kept) self where
  older := context.older
  located := context.located.transport registry
  reachable := context.reachable
  smaller := by
    obtain ⟨newer, changed, _⟩ := registry
    rw [changed, List.length_append]
    have shorter := context.smaller
    omega

/-- Child expansion is the existing source operation on the installation's
older registry and the parent's source-relative expansion path. -/
def SourceContext.operations (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (child : OracleRead) (state : S × Nat) :
    PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value child.kind.answer)) :=
  OracleProcess.answer model self context.older ((parent.request site expansion).expand child) state

theorem SourceContext.transport_operations (context : SourceContext parent self)
    {newReferences : CaptureLayout.References}
    {newEntries : OracleEntries model snapshot domains math}
    {newRecords : List (model.Value layout.recordType)}
    (registry : OracleStore.FreshExtension entries newEntries) (physical : records <+: newRecords)
    (kept : ∀ kind identity anchor reference,
      references kind identity anchor reference → newReferences kind identity anchor reference)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (child : OracleRead) (state : S × Nat) :
    (context.transport registry physical kept).operations (E := E) site expansion child state =
      context.operations site expansion child state := rfl

/-- The original query's result mapping preserves stops and rejects absent
answers. The query event precedes the complete body log on every outcome. -/
def Parent.finish (parent : Parent layout references entries records frame)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (result : PIR.Execution (S × Nat) (OracleEvent E)
      (Values (Component model.Value) [checked.declaration.kind.answer])) :
    PIR.Execution (S × Nat) (OracleEvent E) (model.Value checked.declaration.kind.answer) :=
  ⟨match result.outcome with
    | .stopped reason => .stopped reason
    | .returned values => match values.get .here with
      | none => .stopped .incomplete
      | some value => .returned value,
    result.state, .query (parent.request site expansion) :: result.events⟩

theorem SourceContext.expands (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (allowed : OracleStore.visible self parent.holder parent.receivers = true)
    (shape : OracleStore.validRows checked.declaration.kind parent.rows = true)
    (inside : frame.position < parent.rows) (state : S × Nat) :
    OracleProcess.answer (E := E) model self entries (parent.request site expansion) state =
      OracleProcess.mapResult (parent.finish site expansion)
        (OracleProcess.present (context.operations site expansion) parent.body
          (state.1, state.2 + 1)) :=
  OracleProcess.answer_virtual checked (parent.request site expansion) rfl
    parent.rows parent.holder parent.receivers parent.captures context.located
    parent.signature self allowed shape inside state

/-- Reconnect a real body execution to its original parent query. This uses
no successful-outcome restriction and keeps its logical query charge. -/
theorem SourceContext.reached (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (allowed : OracleStore.visible self parent.holder parent.receivers = true)
    (shape : OracleStore.validRows checked.declaration.kind parent.rows = true)
    (inside : frame.position < parent.rows)
    (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (state : S × Nat) (initial final : interaction.Phase)
    (result : PIR.Execution (S × Nat) (OracleEvent E)
      (Values (Component model.Value) [checked.declaration.kind.answer]))
    (body : PIR.Reaches interaction
      (OracleProcess.present (context.operations site expansion) parent.body (state.1, state.2 + 1))
      initial (.done result) final) :
    PIR.Reaches interaction
      (OracleProcess.answer model self entries (parent.request site expansion) state)
      initial (.done (parent.finish site expansion result)) final := by
  rw [context.expands site expansion allowed shape inside state]
  exact body.bind (fun result ↦ .done (parent.finish site expansion result))

/-- Completing the actual source-progress derivation returns the same answer
from the original parent query. The child's provider state and ordered events
remain those derived by the shared resumption rules. -/
theorem SourceContext.completed (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (allowed : OracleStore.visible self parent.holder parent.receivers = true)
    (shape : OracleStore.validRows checked.declaration.kind parent.rows = true)
    (inside : frame.position < parent.rows)
    (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (state after : S × Nat) (initial final : interaction.Phase)
    (arenas : (kind : OracleKind) → List (model.Value kind.answer)) (indices : List Nat)
    (answer : model.Value checked.declaration.kind.answer) (events : List (OracleEvent E))
    (body : QuerySourceContinuation.Produced interaction (context.operations site expansion)
      parent.body (state.1, state.2 + 1) initial arenas
      (.done (.cons (some answer) .nil)) indices after final events) :
    PIR.Reaches interaction
      (OracleProcess.answer model self entries (parent.request site expansion) state)
      initial
      (.done ⟨.returned answer, after, .query (parent.request site expansion) :: events⟩)
      final :=
  context.reached site expansion allowed shape inside interaction state initial final _ body.completed

end Zkc.Realization.QuerySavedSource
