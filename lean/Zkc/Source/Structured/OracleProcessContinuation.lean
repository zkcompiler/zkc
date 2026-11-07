module

public import Zkc.Source.Structured.OracleProcess
public import Zkc.Semantics.InteractionContinuation

@[expose] public section

/-! Cutting and restoring an original source continuation preserves its whole
execution record. A saved parent resumes only after a returned child; stopped
children retain their final provider state and ordered events. These are laws
of the existing free presentation, independent of a provider or protocol.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {I J : PIR.Signature} {S E A B C : Type}

/-- The source's already observed event prefix surrounds its remaining
execution without changing the state, result or external operations. -/
def prependEvents (events : List E) (process : PIR.Process J (PIR.Execution S E A)) :
    PIR.Process J (PIR.Execution S E A) :=
  mapResult (fun result ↦ {result with events := events ++ result.events}) process

theorem prependEvents_nil (process : PIR.Process J (PIR.Execution S E A)) :
    prependEvents [] process = process := by
  simp only [prependEvents, mapResult, List.nil_append]
  exact PIR.Process.bind_done _

theorem prependEvents_append (first second : List E)
    (process : PIR.Process J (PIR.Execution S E A)) :
    prependEvents first (prependEvents second process) =
      prependEvents (first ++ second) process := by
  simp only [prependEvents, mapResult, PIR.Process.bind_assoc, PIR.Process.bind, List.append_assoc]

theorem prependEvents_reaches {P : PIR.Interaction J}
    {first last : PIR.Process J (PIR.Execution S E A)} {initial final : P.Phase}
    (path : PIR.Reaches P first initial last final) (events : List E) :
    PIR.Reaches P (prependEvents events first) initial (prependEvents events last) final :=
  path.bind _

/-- Actual returned child execution reaches the next original source
continuation. Both its poststate and ordered events are retained. -/
theorem present_returned {P : PIR.Interaction J}
    (operations : (operation : I.Op) → S →
      PIR.Process J (PIR.Execution S E (I.Reply operation)))
    (operation : I.Op) (next : I.Reply operation → PIR.Process I A)
    {before after : S} {events : List E} {reply : I.Reply operation}
    {initial final : P.Phase}
    (path : PIR.Reaches P (operations operation before) initial
      (.done ⟨.returned reply, after, events⟩) final) :
    PIR.Reaches P (present operations (.call operation next) before) initial
      (prependEvents events (present operations (next reply) after)) final :=
  path.bind (fun result ↦ sequence result fun value state ↦ present operations (next value) state)

/-- A stopped child reaches the same stopped source record. No next source
query is evaluated and no returned reply can be saved on this path. -/
theorem present_stopped {P : PIR.Interaction J}
    (operations : (operation : I.Op) → S →
      PIR.Process J (PIR.Execution S E (I.Reply operation)))
    (operation : I.Op) (next : I.Reply operation → PIR.Process I A)
    {before after : S} {events : List E} {reason : PIR.Stop}
    {initial final : P.Phase}
    (path : PIR.Reaches P (operations operation before) initial
      (.done ⟨.stopped reason, after, events⟩) final) :
    PIR.Reaches P (present operations (.call operation next) before) initial
      (.done ⟨.stopped reason, after, events⟩) final :=
  path.bind (fun result ↦ sequence result fun value state ↦ present operations (next value) state)

/-- Reassociate nested source continuations without changing the effect tree,
including the prefix of events and state at every stopped result. -/
theorem sequence_assoc (first : PIR.Execution S E A)
    (next : A → S → PIR.Process J (PIR.Execution S E B))
    (last : B → S → PIR.Process J (PIR.Execution S E C)) :
    (sequence first next).bind (fun result ↦ sequence result last) =
      sequence first (fun value state ↦
        (next value state).bind fun result ↦ sequence result last) := by
  rcases first with ⟨outcome, state, events⟩
  cases outcome with
  | stopped reason => rfl
  | returned value =>
      simp only [sequence, PIR.Process.bind_assoc]
      congr 1
      funext result
      rcases result with ⟨outcome, state, following⟩
      cases outcome with
      | stopped reason => rfl
      | returned value =>
          simp only [PIR.Process.bind_assoc, PIR.Process.bind]
          congr 1
          funext result
          simp only [List.append_assoc]

/-- A cut in the original body composes through its actual stateful query
expansion. This equation does not choose a handler, drop a failed branch, or
assume that a mathematical helper or child query returns. -/
theorem present_bind
    (operations : (operation : I.Op) → S →
      PIR.Process J (PIR.Execution S E (I.Reply operation)))
    (body : PIR.Process I A) (next : A → PIR.Process I B) (state : S) :
    present operations (body.bind next) state =
      (present operations body state).bind (fun result ↦
        sequence result (fun value current ↦ present operations (next value) current)) := by
  induction body generalizing state with
  | done value =>
      simp only [present, PIR.Process.bind, sequence, List.nil_append]
      exact (PIR.Process.bind_done _).symm
  | halt reason => rfl
  | call operation continuation ih =>
      simp only [PIR.Process.bind, present, PIR.Process.bind_assoc]
      congr 1
      funext result
      rw [sequence_assoc]
      congr 1
      funext reply current
      exact ih reply current

end Zkc.Source.Structured.OracleProcess
