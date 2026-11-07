module

public import Zkc.Realization.QuerySourceContext

@[expose] public section

/-! Suspend an installed source query at its actual child operation. Nested
parents compose with the existing `Reaches.bind` rule; no separate stack
evaluator or protocol-specific continuation invariant is introduced here.
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
  {parent : Parent layout references entries records frame} {self : Nat} {S E : Type}

/-- The suspended parent's existing source continuation, including its prior
events and enclosing query event. The child reply carries its actual poststate
and outcome; a stopped reply never invokes the next source continuation. -/
def SourceContext.restore (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    {request : OracleRead}
    (next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer]))
    (events : List (OracleEvent E))
    (result : PIR.Execution (S × Nat) (OracleEvent E) (model.Value request.kind.answer)) :
    PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value checked.declaration.kind.answer)) :=
  OracleProcess.mapResult (parent.finish site expansion)
    (OracleProcess.prependEvents events
      (OracleProcess.sequence result fun answer state ↦
        OracleProcess.present (context.operations site expansion) (next answer) state))

theorem SourceContext.restore_returned (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    {request : OracleRead}
    (next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer]))
    (events following : List (OracleEvent E)) (answer : model.Value request.kind.answer)
    (state : S × Nat) :
    context.restore site expansion next events ⟨.returned answer, state, following⟩ =
      OracleProcess.mapResult (parent.finish site expansion)
        (OracleProcess.prependEvents (events ++ following)
          (OracleProcess.present (context.operations site expansion) (next answer) state)) := by
  change OracleProcess.mapResult (parent.finish site expansion)
    (OracleProcess.prependEvents events (OracleProcess.prependEvents following
      (OracleProcess.present (context.operations site expansion) (next answer) state))) = _
  rw [OracleProcess.prependEvents_append]

theorem SourceContext.restore_stopped (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    {request : OracleRead}
    (next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer]))
    (events following : List (OracleEvent E)) (reason : PIR.Stop) (state : S × Nat) :
    context.restore site expansion next events ⟨.stopped reason, state, following⟩ =
      .done ⟨.stopped reason, state,
        .query (parent.request site expansion) :: (events ++ following)⟩ := rfl

/-- The actual parent query reaches precisely the child's operation with its
saved source continuation attached. This retains the initial query charge,
already produced replies, interaction phase and all enclosing source paths. -/
theorem SourceContext.suspended (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (allowed : OracleStore.visible self parent.holder parent.receivers = true)
    (shape : OracleStore.validRows checked.declaration.kind parent.rows = true)
    (inside : frame.position < parent.rows)
    (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    {initial current : S × Nat} {initialPhase currentPhase : interaction.Phase}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {indices : List Nat}
    {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer])}
    {events : List (OracleEvent E)}
    (produced : QuerySourceContinuation.Produced interaction (context.operations site expansion)
      parent.body (initial.1, initial.2 + 1) initialPhase arenas
      (.call request next) indices current currentPhase events) :
    PIR.Reaches interaction
      (OracleProcess.answer model self entries (parent.request site expansion) initial) initialPhase
      ((context.operations site expansion request current).bind
        (context.restore site expansion next events)) currentPhase := by
  rw [context.expands site expansion allowed shape inside initial]
  have reached := produced.executed.bind (fun result ↦ .done (parent.finish site expansion result))
  unfold SourceContext.restore
  simpa only [OracleProcess.present, OracleProcess.prependEvents, OracleProcess.mapResult,
    PIR.Process.bind_assoc, PIR.Process.bind] using reached

/-- A completed child reconnects through the same suspended continuation.
Applying this at successive installed parents composes arbitrary nesting with
ordinary process bind, including stopped children and their resource usage. -/
theorem SourceContext.child_reached (context : SourceContext parent self)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (allowed : OracleStore.visible self parent.holder parent.receivers = true)
    (shape : OracleStore.validRows checked.declaration.kind parent.rows = true)
    (inside : frame.position < parent.rows)
    (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    {initial current : S × Nat} {initialPhase currentPhase finalPhase : interaction.Phase}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {indices : List Nat}
    {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer])}
    {events : List (OracleEvent E)}
    (produced : QuerySourceContinuation.Produced interaction (context.operations site expansion)
      parent.body (initial.1, initial.2 + 1) initialPhase arenas
      (.call request next) indices current currentPhase events)
    (result : PIR.Execution (S × Nat) (OracleEvent E) (model.Value request.kind.answer))
    (child : PIR.Reaches interaction (context.operations site expansion request current)
      currentPhase (.done result) finalPhase) :
    PIR.Reaches interaction
      (OracleProcess.answer model self entries (parent.request site expansion) initial) initialPhase
      (context.restore site expansion next events result) finalPhase :=
  (context.suspended site expansion allowed shape inside interaction produced).trans (child.bind _)

end Zkc.Realization.QuerySavedSource
