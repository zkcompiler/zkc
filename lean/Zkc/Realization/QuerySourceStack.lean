module

public import Zkc.Realization.QuerySourceSuspension

@[expose] public section

/-! The source meaning of the controller's linked continuation frames. Each
link uses its actual saved slot and installed parent. Its outer coordinates
index the remaining stack, so an independently valid frame cannot silently
select a different caller. Restoration is composition of existing source
continuations; this module introduces no oracle evaluator.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Realization.QuerySourceStack
open Zkc.Source Zkc.Source.Structured QuerySavedSource

inductive Stack (model : DomainModel) (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) (self : Nat) (S E : Type) (root : OracleKind) :
    OracleKind → Nat → Nat → Type where
  | root : Stack model snapshot domains math self S E root root 0 0
  | saved {checked : CheckedOracle snapshot domains math}
      {layout : VirtualStorage.Layout checked.declaration.inputs.dropLast}
      {references : CaptureLayout.References} {entries : OracleEntries model snapshot domains math}
      {records : List (model.Value layout.recordType)} {frame : QueryContinuation.Frame}
      {parent : Parent layout references entries records frame}
      (context : SourceContext parent self)
      {identity : String} {count slot : Nat}
      {frames : List (model.Value (QueryContinuation.layout identity count).type)}
      {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
      {request : OracleRead}
      {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
        (Values (Component model.Value) [checked.declaration.kind.answer])}
      (saved : Saved identity count frames slot arenas parent request next)
      (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
      (events : List (OracleEvent E)) (tag : Nat)
      (outer : Stack model snapshot domains math self S E root checked.declaration.kind
        frame.outer frame.outerInstance) :
      Stack model snapshot domains math self S E root request.kind (tag + 1) slot

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {self : Nat} {S E : Type} {root current : OracleKind}
  {tag slot : Nat}

def Stack.restore : {current : OracleKind} → {tag slot : Nat} →
    Stack model snapshot domains math self S E root current tag slot →
    PIR.Execution (S × Nat) (OracleEvent E) (model.Value current.answer) →
    PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))
  | _, _, _, .root, result => .done result
  | _, _, _, .saved (next := next) context _ site expansion events _ outer, result =>
      (context.restore site expansion next events result).bind outer.restore

/-- The prefix records the outermost source query first. Already produced
siblings retain their complete ordered logs between parent query events. -/
def Stack.events : {current : OracleKind} → {tag slot : Nat} →
    Stack model snapshot domains math self S E root current tag slot → List (OracleEvent E)
  | _, _, _, .root => []
  | _, _, _, .saved (parent := parent) _ _ site expansion events _ outer =>
      outer.events ++ (.query (parent.request site expansion) :: events)

/-- Every saved link must still be resident in the controller's current
physical stores. The historical frame and answer snapshots are immutable
prefixes, not independent arrays selected when a continuation is restored. -/
def Stack.Resident
    (arenas : (kind : OracleKind) → List (model.Value kind.answer))
    (frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)) :
    {current : OracleKind} → {tag slot : Nat} →
    Stack model snapshot domains math self S E root current tag slot → Prop
  | _, _, _, .root => True
  | _, _, _, .saved (identity := identity) (count := count) (frames := savedFrames)
      (arenas := savedArenas) _ _ _ _ _ _ outer =>
      savedFrames <+: frames identity count ∧
        (∀ kind, savedArenas kind <+: arenas kind) ∧ outer.Resident arenas frames

theorem Stack.Resident.transport
    {arenas nextArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {frames nextFrames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    {stack : Stack model snapshot domains math self S E root current tag slot}
    (resident : stack.Resident arenas frames)
    (answers : ∀ kind, arenas kind <+: nextArenas kind)
    (saved : ∀ identity count, frames identity count <+: nextFrames identity count) :
    stack.Resident nextArenas nextFrames := by
  induction stack with
  | root => trivial
  | saved context link site expansion events selection outer ih =>
      exact ⟨resident.1.trans (saved _ _),
        fun kind ↦ (resident.2.1 kind).trans (answers kind), ih resident.2.2⟩

theorem Stack.restore_stopped
    (stack : Stack model snapshot domains math self S E root current tag slot)
    (reason : PIR.Stop) (state : S × Nat) (following : List (OracleEvent E)) :
    stack.restore ⟨.stopped reason, state, following⟩ =
      .done ⟨.stopped reason, state, stack.events ++ following⟩ := by
  induction stack generalizing following with
  | root => rfl
  | saved context saved site expansion events tag outer ih =>
      simp only [Stack.restore, SourceContext.restore_stopped, PIR.Process.bind]
      rw [ih]
      simp only [Stack.events, List.append_assoc, List.cons_append]

/-- Physical return coordinates are intrinsic to the stack index. Only the
root has continuation zero, independently of any answer's value or type. -/
theorem Stack.zero_root
    (stack : Stack model snapshot domains math self S E root current 0 slot) :
    current = root ∧ slot = 0 := by cases stack; exact ⟨rfl, rfl⟩

/-- The root starts before any provider work or saved parent. -/
theorem initial (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (entries : OracleEntries model snapshot domains math) (request : OracleRead)
    (state : S × Nat) (phase : interaction.Phase) :
    PIR.Reaches interaction (OracleProcess.answer model self entries request state) phase
      ((OracleProcess.answer model self entries request state).bind
        (Stack.restore (.root : Stack model snapshot domains math self S E
          request.kind request.kind 0 0))) phase := by
  simpa only [Stack.restore, PIR.Process.bind_done] using
    (PIR.Reaches.refl (P := interaction)
      (OracleProcess.answer model self entries request state) phase)

/-- Descend through a real saved frame. Source execution determines the child
operation; the frame determines its physical slot and outer stack. The root
connection composes without a protocol-specific stack or phase invariant. -/
theorem descend
    {checked : CheckedOracle snapshot domains math}
    {layout : VirtualStorage.Layout checked.declaration.inputs.dropLast}
    {references : CaptureLayout.References} {entries : OracleEntries model snapshot domains math}
    {records : List (model.Value layout.recordType)} {frame : QueryContinuation.Frame}
    {parent : Parent layout references entries records frame}
    (context : SourceContext parent self)
    {identity : String} {count cell : Nat}
    {frames : List (model.Value (QueryContinuation.layout identity count).type)}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer])}
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (events : List (OracleEvent E)) (selection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    (allowed : OracleStore.visible self parent.holder parent.receivers = true)
    (shape : OracleStore.validRows checked.declaration.kind parent.rows = true)
    (inside : frame.position < parent.rows)
    (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial now : S × Nat} {start entered phase : interaction.Phase}
    (reached : PIR.Reaches interaction source start
      ((OracleProcess.answer model self entries (parent.request site expansion) initial).bind
        outer.restore) entered)
    (produced : QuerySourceContinuation.Produced interaction (context.operations site expansion)
      parent.body (initial.1, initial.2 + 1) entered arenas (.call request next)
      frame.answers now phase events) :
    PIR.Reaches interaction source start
      ((context.operations site expansion request now).bind
        (Stack.restore (.saved context saved site expansion events selection outer))) phase := by
  have child := (context.suspended site expansion allowed shape inside interaction produced).bind
    outer.restore
  simpa only [Stack.restore, PIR.Process.bind_assoc] using reached.trans child

/-- A completed child resumes the stored source continuation chain. The
returned value and its provider history are the actual child's execution. -/
theorem returned (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (stack : Stack model snapshot domains math self S E root current tag slot)
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {pending : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value current.answer))}
    {start phase final : interaction.Phase}
    (reached : PIR.Reaches interaction source start (pending.bind stack.restore) phase)
    (result : PIR.Execution (S × Nat) (OracleEvent E) (model.Value current.answer))
    (child : PIR.Reaches interaction pending phase (.done result) final) :
    PIR.Reaches interaction source start (stack.restore result) final :=
  reached.trans (child.bind stack.restore)

/-- A stopped child unwinds every saved parent and retains its exact poststate
and ordered source/provider log. No continuation receives a fabricated answer. -/
theorem stopped (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (stack : Stack model snapshot domains math self S E root current tag slot)
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {pending : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value current.answer))}
    {start phase final : interaction.Phase}
    (reached : PIR.Reaches interaction source start (pending.bind stack.restore) phase)
    (reason : PIR.Stop) (state : S × Nat) (following : List (OracleEvent E))
    (child : PIR.Reaches interaction pending phase
      (.done ⟨.stopped reason, state, following⟩) final) :
    PIR.Reaches interaction source start
      (.done ⟨.stopped reason, state, stack.events ++ following⟩) final := by
  simpa only [stack.restore_stopped] using returned interaction stack reached _ child

section Return
variable {checked : CheckedOracle snapshot domains math}
  {layout : VirtualStorage.Layout checked.declaration.inputs.dropLast}
  {references : CaptureLayout.References} {entries : OracleEntries model snapshot domains math}
  {records : List (model.Value layout.recordType)} {frame : QueryContinuation.Frame}
  {parent : Parent layout references entries records frame}
  {identity : String} {count cell : Nat}
  {frames : List (model.Value (QueryContinuation.layout identity count).type)}
  {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
  {request : OracleRead}
  {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
    (Values (Component model.Value) [checked.declaration.kind.answer])}

/-- The return dispatcher moves to the actual next source operation. The old
parent event and the child's complete log become the saved prefix for that
sibling; the outer stack and original installation context are unchanged. -/
theorem Stack.restore_sibling
    (context : SourceContext parent self)
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (events followingEvents : List (OracleEvent E)) (selection nextSelection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    (answer : model.Value request.kind.answer) (state : S × Nat)
    {currentArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    (retained : ∀ kind, arenas kind <+: currentArenas kind)
    {answerSlot : Nat}
    (returned : (currentArenas request.kind)[answerSlot]? = some answer)
    {following : OracleRead}
    {continuation : model.Value following.kind.answer →
      PIR.Process (oracleReadInterface model.toCarriers)
        (Values (Component model.Value) [checked.declaration.kind.answer])}
    (nextQuery : next answer = .call following continuation)
    (nextIdentity : String) (nextCount : Nat)
    (nextFrames : List (model.Value (QueryContinuation.layout nextIdentity nextCount).type))
    {record : model.Value (QueryContinuation.layout nextIdentity nextCount).type}
    (encoded : QueryContinuation.Encodes nextIdentity nextCount
      {frame with answers := frame.answers ++ [answerSlot]} record) :
    (Stack.saved context saved site expansion events selection outer).restore
      ⟨.returned answer, state, followingEvents⟩ =
    (context.operations site expansion following state).bind
      (Stack.restore (.saved (context.withAnswers (frame.answers ++ [answerSlot]))
        (saved.sibling retained returned nextQuery nextIdentity nextCount nextFrames encoded)
        site expansion (events ++ followingEvents) nextSelection outer)) := by
  simp only [Stack.restore, SourceContext.restore_returned, nextQuery, OracleProcess.present]
  simp only [SourceContext.restore, OracleProcess.prependEvents, OracleProcess.mapResult,
    PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

/-- Completing the last child returns its parent's actual answer through the
outer continuation. No provider call, query charge or phase transition is
invented by this administrative return; all of those are already in the child
record and saved prefix. -/
theorem Stack.restore_parent
    (context : SourceContext parent self)
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (events following : List (OracleEvent E)) (selection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    (answer : model.Value request.kind.answer) (state : S × Nat)
    (parentAnswer : model.Value checked.declaration.kind.answer)
    (finished : next answer = .done (.cons (some parentAnswer) .nil)) :
    (Stack.saved context saved site expansion events selection outer).restore
      ⟨.returned answer, state, following⟩ =
    outer.restore ⟨.returned parentAnswer, state,
      .query (parent.request site expansion) :: (events ++ following)⟩ := by
  simp only [Stack.restore, SourceContext.restore_returned, finished,
    OracleProcess.present, OracleProcess.prependEvents, OracleProcess.mapResult,
    PIR.Process.bind, Parent.finish, Values.get, List.append_nil]

/-- A failed parent calculation stops through every outer frame. It cannot
be replaced by a successful parent answer merely because the child returned. -/
theorem Stack.restore_parent_stopped
    (context : SourceContext parent self)
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (events following : List (OracleEvent E)) (selection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    (answer : model.Value request.kind.answer) (state : S × Nat)
    (reason : PIR.Stop) (stopped : next answer = .halt reason) :
    (Stack.saved context saved site expansion events selection outer).restore
      ⟨.returned answer, state, following⟩ =
    .done ⟨.stopped reason, state,
      outer.events ++ .query (parent.request site expansion) :: (events ++ following)⟩ := by
  simp only [Stack.restore, SourceContext.restore_returned, stopped,
    OracleProcess.present, OracleProcess.prependEvents, OracleProcess.mapResult,
    PIR.Process.bind, Parent.finish, List.append_nil]
  exact outer.restore_stopped reason state _

end Return
end Zkc.Realization.QuerySourceStack
