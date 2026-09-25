import Zkc.Modules.ImmutableCache

set_option autoImplicit false

namespace Zkc.Protocols.CommitmentSessions
abbrev SessionId := Bool
inductive Phase where
  | fresh | committed (c : Nat) | done | cancelled | failed
  deriving DecidableEq, Repr
inductive Command where
  | commit | reveal | open (m r : Nat) | cancel
  deriving DecidableEq, Repr
structure Action where
  sid : SessionId
  cmd : Command
  deriving DecidableEq, Repr
inductive Message where
  | commitment (c : Nat) | opening (m r : Nat) | accept | reject | cancel | invalid
  deriving DecidableEq, Repr
abbrev Event := SessionId × Message
structure Input where
  key : Nat
  message : Nat
  coin : Nat
  deriving Repr

/-- Provider realization is a common contract; no security axioms. -/
structure Provider (T : Type) where
  prepare : Nat → T
  commit : Nat → T → Nat → Nat → Nat
  verify : Nat → Nat → Nat → Nat → Bool

abbrev Cache (T : Type) := Modules.ImmutableCache.Cache Nat T
abbrev Valid {T : Type} (p : Provider T) (cache : Cache T) : Prop :=
  Modules.ImmutableCache.Valid p.prepare cache

abbrev put {T : Type} (cache : Cache T) (k : Nat) (t : T) : Cache T :=
  Modules.ImmutableCache.insert cache k t

def acquire {T : Type} (p : Provider T) (share : Bool) (cache : Cache T) (k : Nat) :
    T × Cache T × Nat :=
  if share then
    match cache k with
    | some t => (t, cache, 0)
    | none => let t := p.prepare k; (t, put cache k t, 1)
  else (p.prepare k, cache, 1)

theorem put_valid {T : Type} (p : Provider T) (cache : Cache T) (h : Valid p cache)
    (k : Nat) : Valid p (put cache k (p.prepare k)) :=
  Modules.ImmutableCache.insert_valid p.prepare cache h k

theorem acquire_correct {T : Type} (p : Provider T) (share : Bool) (cache : Cache T)
    (k : Nat) (h : Valid p cache) :
    (acquire p share cache k).1 = p.prepare k ∧
      Valid p (acquire p share cache k).2.1 := by
  cases share
  · exact ⟨rfl, h⟩
  · cases hk : cache k with
    | none => simpa [acquire, hk] using And.intro (Eq.refl (p.prepare k)) (put_valid p cache h k)
    | some t => simpa [acquire, hk] using And.intro (h k t hk) h

/-- A request is atomic; cancellation occurs only between these requests. -/
def localTransition (check : Nat → Nat → Nat → Bool) (make : Nat → Nat → Nat)
    (i : Input) (phase : Phase) (cmd : Command) : Phase × List Message :=
  match phase, cmd with
  | .fresh, .commit => let c := make i.message i.coin; (.committed c, [.commitment c])
  | .committed c, .reveal =>
      if check c i.message i.coin then (.done, [.opening i.message i.coin, .accept])
      else (.failed, [.opening i.message i.coin, .reject])
  | .committed c, .open m r =>
      if check c m r then (.done, [.opening m r, .accept])
      else (.failed, [.opening m r, .reject])
  | .fresh, .cancel | .committed _, .cancel => (.cancelled, [.cancel])
  | _, _ => (phase, [.invalid])

def needs : Phase → Command → Bool
  | .fresh, .commit => true
  | _, _ => false

structure State (T : Type) where
  sessions : SessionId → Phase
  cache : Cache T
  trace : List Event
  builds : Nat

def initial {T : Type} : State T := ⟨fun _ => .fresh, fun _ => none, [], 0⟩

def finish {T : Type} (s : State T) (a : Action) (next : Phase × List Message)
    (cache : Cache T) (work : Nat) : State T :=
  ⟨fun j => if j = a.sid then next.1 else s.sessions j,
   cache, s.trace ++ next.2.map (fun m => (a.sid, m)), s.builds + work⟩

def step {T : Type} (p : Provider T) (inputs : SessionId → Input) (share : Bool)
    (s : State T) (a : Action) : State T :=
  let i := inputs a.sid
  if needs (s.sessions a.sid) a.cmd then
    let ac := acquire p share s.cache i.key
    finish s a (localTransition (p.verify i.key) (p.commit i.key ac.1) i (s.sessions a.sid) a.cmd)
      ac.2.1 ac.2.2
  else
    finish s a (localTransition (p.verify i.key) (fun _ _ => 0) i (s.sessions a.sid) a.cmd) s.cache 0

/-- Equality of all local phases and the exact ordered global protocol trace. -/
def Related {T : Type} (p : Provider T) (s t : State T) : Prop :=
  s.sessions = t.sessions ∧ s.trace = t.trace ∧ Valid p s.cache ∧ Valid p t.cache

theorem finish_related {T : Type} (p : Provider T) (s t : State T)
    (h : Related p s t) (a : Action) (next : Phase × List Message)
    (cs ct : Cache T) (hs : Valid p cs) (ht : Valid p ct) (ws wt : Nat) :
    Related p (finish s a next cs ws) (finish t a next ct wt) := by
  exact ⟨by simp only [finish, h.1], by simp only [finish, h.2.1], hs, ht⟩

theorem step_related {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (s t : State T) (h : Related p s t) (a : Action) :
    Related p (step p inputs false s a) (step p inputs true t a) := by
  simp only [step, ← h.1]
  split
  · have hs := acquire_correct p false s.cache (inputs a.sid).key h.2.2.1
    have ht := acquire_correct p true t.cache (inputs a.sid).key h.2.2.2
    rw [hs.1, ht.1]
    exact finish_related p s t h a _ _ _ hs.2 ht.2 _ _
  · exact finish_related p s t h a _ _ _ h.2.2.1 h.2.2.2 _ _

def run {T : Type} (p : Provider T) (inputs : SessionId → Input) (share : Bool) :
    List Action → State T → State T
  | [], s => s
  | a :: rest, s => run p inputs share rest (step p inputs share s a)

theorem run_related {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (actions : List Action) (s t : State T) (h : Related p s t) :
    Related p (run p inputs false actions s) (run p inputs true actions t) := by
  induction actions generalizing s t with
  | nil => exact h
  | cons a rest ih => exact ih _ _ (step_related p inputs s t h a)

theorem initial_related {T : Type} (p : Provider T) : Related p initial initial := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro k t h <;> cases h

theorem exact_global_trace {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (actions : List Action) :
    (run p inputs false actions initial).trace = (run p inputs true actions initial).trace :=
  (run_related p inputs actions initial initial (initial_related p)).2.1

abbrev Scheduler := List Event → Option Action

def adaptive {T : Type} (p : Provider T) (inputs : SessionId → Input) (share : Bool)
    (scheduler : Scheduler) : Nat → State T → State T
  | 0, s => s
  | n+1, s => match scheduler s.trace with
    | none => s
    | some a => adaptive p inputs share scheduler n (step p inputs share s a)

theorem adaptive_related {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (scheduler : Scheduler) (n : Nat) (s t : State T) (h : Related p s t) :
    Related p (adaptive p inputs false scheduler n s)
      (adaptive p inputs true scheduler n t) := by
  induction n generalizing s t with
  | zero => exact h
  | succ n ih =>
    simp only [adaptive, ← h.2.1]
    cases scheduler s.trace with
    | none => exact h
    | some a => exact ih _ _ (step_related p inputs s t h a)

/-- Every observer of this trace, including a role/session projection, transports. -/
theorem adaptive_observer {T O : Type} (p : Provider T) (inputs : SessionId → Input)
    (scheduler : Scheduler) (n : Nat) (observe : List Event → O) :
    observe (adaptive p inputs false scheduler n initial).trace =
      observe (adaptive p inputs true scheduler n initial).trace :=
  congrArg observe (adaptive_related p inputs scheduler n initial initial (initial_related p)).2.1

def role (sid : SessionId) (trace : List Event) : List Message :=
  (trace.filter (fun e => e.1 == sid)).map Prod.snd

/-- A local update frames the other session, independently of shared-table state. -/
theorem other_session_frame {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (share : Bool) (s : State T) (a : Action) (j : SessionId) (hj : j ≠ a.sid) :
    (step p inputs share s a).sessions j = s.sessions j := by
  simp only [step]
  split <;> simp [finish, hj]

theorem acquire_work_bound {T : Type} (p : Provider T) (cache : Cache T) (k : Nat) :
    (acquire p true cache k).2.2 ≤ 1 := by
  cases hk : cache k <;> simp [acquire, hk]

theorem step_builds_le {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (s t : State T) (h : Related p s t) (hc : t.builds ≤ s.builds) (a : Action) :
    (step p inputs true t a).builds ≤ (step p inputs false s a).builds := by
  simp only [step, ← h.1]
  split
  · exact Nat.add_le_add hc (acquire_work_bound p t.cache (inputs a.sid).key)
  · exact Nat.add_le_add_right hc 0

theorem run_builds_le {T : Type} (p : Provider T) (inputs : SessionId → Input)
    (actions : List Action) (s t : State T) (h : Related p s t) (hc : t.builds ≤ s.builds) :
    (run p inputs true actions t).builds ≤ (run p inputs false actions s).builds := by
  induction actions generalizing s t with
  | nil => exact hc
  | cons a rest ih =>
    exact ih _ _ (step_related p inputs s t h a) (step_builds_le p inputs s t h hc a)

/-- Pure local transitions on distinct session state commute. This does NOT swap traces. -/
def updateSession (f : SessionId → Phase → Phase) (sid : SessionId) (state : SessionId → Phase) : SessionId → Phase :=
  fun j => if j = sid then f sid (state sid) else state j

theorem independent_updates (f g : SessionId → Phase → Phase) (a b : SessionId)
    (hne : a ≠ b) (state : SessionId → Phase) :
    updateSession g b (updateSession f a state) = updateSession f a (updateSession g b state) := by
  funext j
  have hrev : b ≠ a := Ne.symm hne
  by_cases ha : j = a
  · subst j
    simp [updateSession, hne]
  · by_cases hb : j = b
    · subst j
      simp [updateSession, hrev]
    · simp [updateSession, ha, hb]

end Zkc.Protocols.CommitmentSessions
