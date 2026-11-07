module

public import Zkc.Realization.QuerySourceStack
public import Zkc.Realization.QueryWork

@[expose] public section

/-! Tie the controller's remaining work to its original source continuation.
The expansion relation is supplied by the checked installation of each child;
this module transports those facts through actual source calls and saved
answers. It does not evaluate an oracle or choose a child's mathematical result.
Stops may leave unused work, but a successful return cannot omit a child. -/
set_option autoImplicit false
namespace Zkc.Realization.QuerySourceWork
open Zkc.Source Zkc.Source.Structured QuerySavedSource QuerySourceStack

variable {model : DomainModel} {A : Type}

/-- A successful source body consumes its ordered child occurrences. A stop
may occur before them. Universality over replies is the static, nonadaptive
query boundary admitted by the current compiler; the reply's mathematics is
not part of this structural schedule. -/
inductive Body (expansion : OracleRead → QueryWork.Shape → Prop) :
    PIR.Process (oracleReadInterface model.toCarriers) A → List QueryWork.Shape → Prop where
  | done (value : A) : Body expansion (.done value) []
  | halt (reason : PIR.Stop) (remaining : List QueryWork.Shape) :
      Body expansion (.halt reason) remaining
  | call (request : OracleRead)
      (next : model.Value request.kind.answer →
        PIR.Process (oracleReadInterface model.toCarriers) A)
      (first : QueryWork.Shape) (rest : List QueryWork.Shape)
      (child : expansion request first) (following : ∀ answer, Body expansion (next answer) rest) :
      Body expansion (.call request next) (first :: rest)

theorem Body.call_iff {expansion : OracleRead → QueryWork.Shape → Prop}
    {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers) A}
    {remaining : List QueryWork.Shape} :
    Body expansion (.call request next) remaining ↔
      ∃ first rest, remaining = first :: rest ∧ expansion request first ∧
        ∀ answer, Body expansion (next answer) rest := by
  constructor
  · intro body
    cases body with
    | call _ _ first rest child following => exact ⟨first, rest, rfl, child, following⟩
  · rintro ⟨first, rest, rfl, child, following⟩
    exact .call _ _ _ _ child following

theorem Body.done_iff {expansion : OracleRead → QueryWork.Shape → Prop} {value : A}
    {remaining : List QueryWork.Shape} :
    Body (model := model) expansion (.done value) remaining ↔ remaining = [] := by
  constructor
  · intro body; cases body; rfl
  · rintro rfl; exact .done _

/-- Reaching an actual continuation consumes one scheduled occurrence for
each actual source reply, including equal-valued and repeated-handle replies. -/
theorem Body.reached {expansion : OracleRead → QueryWork.Shape → Prop}
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {before after : QuerySourceContinuation.Answers model} {remaining : List QueryWork.Shape}
    (body : Body expansion source remaining)
    (path : PIR.Reaches (QuerySourceContinuation.interaction model) source before residual after) :
    Body expansion residual (remaining.drop (after.kinds.length - before.kinds.length)) := by
  match path with
  | .refl _ _ => simpa using body
  | .step request next initial answer tail final rest =>
      obtain ⟨first, restShapes, rfl, _, following⟩ := Body.call_iff.mp body
      have continued := Body.reached (following answer) rest
      have consumed := QuerySourceContinuation.reached_length rest
      change (initial.kinds ++ [request.kind]).length ≤ final.kinds.length at consumed
      simp only [List.length_append, List.length_cons, List.length_nil] at consumed
      have difference : final.kinds.length - initial.kinds.length =
          (final.kinds.length - (initial.kinds ++ [request.kind]).length) + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [difference, List.drop_succ_cons]
      exact continued

/-- The saved source cursor fixes the remaining work suffix. No separate
ordinal, phase traversal, or guessed number of prior child replies is needed. -/
theorem remaining {expansion : OracleRead → QueryWork.Shape → Prop}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {indices : List Nat} {children : List QueryWork.Shape}
    (body : Body expansion source children)
    (cursor : QuerySourceContinuation.Associated arenas source residual indices) :
    Body expansion residual (children.drop indices.length) := by
  have suffix := body.reached cursor.reached
  simpa only [QuerySourceContinuation.Answers.empty, List.length_nil, Nat.sub_zero,
    ← cursor.width] using suffix

variable {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {self : Nat} {S E : Type} {root current : OracleKind} {tag slot : Nat}

/-- Each actual saved source link retains the remainder of its own parent's
schedule. The older registry and expanded source occurrence are exactly those
used by `SourceContext.operations`. The root has no invented waiting frames. -/
def StackSchedule
    (expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop) :
    {current : OracleKind} → {tag slot : Nat} →
    Stack model snapshot domains math self S E root current tag slot →
      QueryWork.Shape → QueryWork.Frames → Prop
  | _, _, _, .root, _, waiting => waiting = []
  | _, _, _, .saved .., _, [] => False
  | _, _, _, .saved (frame := frame) (parent := parent)
      context _ site path _ _ outer, currentShape, rest :: waiting =>
      ∃ children,
        Body (fun child shape ↦
          expansion context.older ((parent.request site path).expand child) shape)
          parent.body children ∧
        children.drop frame.answers.length = currentShape :: rest ∧
        StackSchedule expansion outer (.virtual children) waiting

/-- A root continuation cannot be assigned saved work, even when all answer
and frame types happen to agree. -/
theorem StackSchedule.root_frames
    {expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop}
    {shape : QueryWork.Shape} {waiting : QueryWork.Frames}
    (scheduled : StackSchedule (self := self) (S := S) (E := E) (root := root)
      expansion .root shape waiting) : waiting = [] := scheduled

/-- Physical continuation zero selects the root, and therefore no saved work
remains. This fact is derived from the linked stack, not supplied by a caller. -/
theorem StackSchedule.zero_frames
    {expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop}
    {stack : Stack model snapshot domains math self S E root current 0 slot}
    {shape : QueryWork.Shape} {waiting : QueryWork.Frames}
    (scheduled : StackSchedule expansion stack shape waiting) : waiting = [] := by
  cases stack
  exact scheduled.root_frames

section Return
variable {checked : CheckedOracle snapshot domains math}
  {layout : VirtualStorage.Layout checked.declaration.inputs.dropLast}
  {references : CaptureLayout.References} {entries : OracleEntries model snapshot domains math}
  {records : List (model.Value layout.recordType)} {frame : QueryContinuation.Frame}
  {parent : Parent layout references entries records frame}
  {identity : String} {count cell : Nat}
  {frames : List (model.Value (QueryContinuation.layout identity count).type)}
  {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {request : OracleRead}
  {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
    (Values (Component model.Value) [checked.declaration.kind.answer])}

/-- The current work shape belongs to the exact pending source operation.
This recovers the child expansion fact and the remaining reply continuation
from the saved cursor and parent schedule, rather than supplying them again. -/
theorem StackSchedule.child
    {expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop}
    (context : SourceContext parent self)
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (path : List (OracleAnchor × OracleLocation))
    (events : List (OracleEvent E)) (selection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    {currentShape : QueryWork.Shape} {rest : List QueryWork.Shape} {waiting : QueryWork.Frames}
    (scheduled : StackSchedule expansion (.saved context saved site path events selection outer)
      currentShape (rest :: waiting)) :
    expansion context.older ((parent.request site path).expand request) currentShape ∧
      ∀ answer, Body (fun child shape ↦
        expansion context.older ((parent.request site path).expand child) shape)
        (next answer) rest := by
  obtain ⟨children, body, suffix, _⟩ := scheduled
  have residual := remaining body saved.cursor
  rw [suffix] at residual
  cases residual with
  | call _ _ _ _ child following => exact ⟨child, following⟩

/-- Sibling dispatch consumes the first actual remaining child and keeps its
parent and outer work. The same answer slot is appended to the physical frame
and used to advance the source cursor; no schedule is chosen independently. -/
theorem StackSchedule.sibling
    {expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop}
    (context : SourceContext parent self)
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (path : List (OracleAnchor × OracleLocation))
    (events followingEvents : List (OracleEvent E)) (selection nextSelection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    {currentShape nextShape : QueryWork.Shape} {rest : List QueryWork.Shape}
    {waiting : QueryWork.Frames}
    (scheduled : StackSchedule expansion (.saved context saved site path events selection outer)
      currentShape ((nextShape :: rest) :: waiting))
    {currentArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    (retained : ∀ kind, arenas kind <+: currentArenas kind)
    {answerSlot : Nat} {answer : model.Value request.kind.answer}
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
    StackSchedule expansion
      (.saved (context.withAnswers (frame.answers ++ [answerSlot]))
        (saved.sibling retained returned nextQuery nextIdentity nextCount nextFrames encoded)
        site path (events ++ followingEvents) nextSelection outer) nextShape (rest :: waiting) := by
  obtain ⟨children, body, suffix, older⟩ := scheduled
  refine ⟨children, body, ?_, older⟩
  have consumed := congrArg (List.drop 1) suffix
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero, List.length_append,
    List.length_cons, List.length_nil] using consumed

/-- Finishing a parent restores that parent's complete shape at the older
stack. The saved cursor's actual number of replies fixes its child count. -/
theorem StackSchedule.complete_parent
    {expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop}
    (context : SourceContext parent self)
    (saved : Saved identity count frames cell arenas parent request next)
    (site : OracleLocation) (path : List (OracleAnchor × OracleLocation))
    (events : List (OracleEvent E)) (selection : Nat)
    (outer : Stack model snapshot domains math self S E root checked.declaration.kind
      frame.outer frame.outerInstance)
    {currentShape : QueryWork.Shape} {waiting : QueryWork.Frames}
    (scheduled : StackSchedule expansion (.saved context saved site path events selection outer)
      currentShape ([] :: waiting)) :
    ∃ children, children.length = frame.answers.length + 1 ∧
      StackSchedule expansion outer (.virtual children) waiting := by
  obtain ⟨children, _, suffix, older⟩ := scheduled
  refine ⟨children, ?_, older⟩
  have length := congrArg List.length suffix
  simp only [List.length_drop, List.length_cons, List.length_nil] at length
  omega
end Return

end Zkc.Realization.QuerySourceWork
