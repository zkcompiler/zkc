import Std

set_option autoImplicit false

namespace PIR

/-- Terminal execution outcomes. Recoverable errors belong to an operation's Reply. -/
inductive Stop where
  | reject | abort | exhausted | incomplete | refused
  deriving DecidableEq, Repr

inductive Outcome (A : Type) where
  | returned : A → Outcome A
  | stopped : Stop → Outcome A
  deriving DecidableEq, Repr

structure Signature where
  Op : Type
  Reply : Op → Type

/-- A well-founded effect tree; not the serialized source grammar.
Each execution path terminates, but reply branching need not be finite and no
uniform bound on the number of calls follows from this type alone. -/
inductive Proc (I : Signature) (A : Type) where
  | done : A → Proc I A
  | halt : Stop → Proc I A
  | call : (o : I.Op) → (I.Reply o → Proc I A) → Proc I A

structure Execution (S E A : Type) where
  outcome : Outcome A
  state : S
  events : List E
  deriving Repr

abbrev Handler (I : Signature) (S E : Type) :=
  (o : I.Op) → S → Execution S E (I.Reply o)

variable {I : Signature} {S T E F O A B : Type}

def Execution.follow (r : Execution S E A) (k : A → S → Execution S E B) :
    Execution S E B :=
  match r.outcome with
  | .stopped why => ⟨.stopped why, r.state, r.events⟩
  | .returned a =>
    let tail := k a r.state
    ⟨tail.outcome, tail.state, r.events ++ tail.events⟩

def Proc.run (h : Handler I S E) : Proc I A → S → Execution S E A
  | .done a, s => ⟨.returned a, s, []⟩
  | .halt why, s => ⟨.stopped why, s, []⟩
  | .call o k, s => (h o s).follow (fun a => (k a).run h)

@[simp] theorem Execution.follow_return (result : Execution S E A) :
    result.follow (fun value state => ⟨.returned value, state, []⟩) = result := by
  rcases result with ⟨outcome, state, events⟩
  cases outcome <;> simp [Execution.follow]

/-- A boundary reset is valid only when the actual successful continuation
cannot distinguish it. A stopped prefix never runs that continuation. -/
theorem Execution.follow_rebase (first : Execution S E A)
    (next : A → S → Execution S E B) (rebase : S → S)
    (compatible : ∀ value, first.outcome = .returned value →
      next value first.state = next value (rebase first.state)) :
    first.follow next = first.follow (fun value state => next value (rebase state)) := by
  cases first with
  | mk outcome state events =>
      cases outcome with
      | stopped why => rfl
      | returned value =>
          have same := compatible value rfl
          simp only [Execution.follow]
          rw [same]

def Proc.bind (p : Proc I A) (k : A → Proc I B) : Proc I B :=
  match p with
  | .done a => k a
  | .halt why => .halt why
  | .call o next => .call o (fun a => (next a).bind k)

theorem follow_assoc {C : Type} (r : Execution S E A)
    (f : A → S → Execution S E B) (g : B → S → Execution S E C) :
    (r.follow f).follow g = r.follow (fun a s => (f a s).follow g) := by
  rcases r with ⟨out,s,es⟩
  cases out with
  | stopped why => rfl
  | returned a =>
    cases hf : f a s with
    | mk result t fs =>
      cases result <;> simp [Execution.follow, hf, List.append_assoc]

theorem run_bind (h : Handler I S E) (p : Proc I A) (k : A → Proc I B) (s : S) :
    (p.bind k).run h s = (p.run h s).follow (fun a => (k a).run h) := by
  induction p generalizing s with
  | done a => simp [Proc.bind, Proc.run, Execution.follow]
  | halt why => rfl
  | call o next ih =>
    simp only [Proc.bind, Proc.run]
    rw [follow_assoc]
    congr 1
    funext a t
    exact ih a t

theorem replacement_then (h : Handler I S E) (p q : Proc I A) (s : S)
    (same : p.run h s = q.run h s) (k : A → Proc I B) :
    (p.bind k).run h s = (q.bind k).run h s := by
  rw [run_bind,run_bind,same]

/-- Projections can erase private events or expand one event into several observations. -/
def observeEvents (view : E → List O) (events : List E) : List O :=
  events.flatMap view

theorem observe_append (view : E → List O) (xs ys : List E) :
    observeEvents view (xs ++ ys) = observeEvents view xs ++ observeEvents view ys := by
  simp [observeEvents]

/-- Equality of reply types is the local-algorithm class, not a codec theorem. -/
structure Related (R : S → T → Prop) (left : E → List O) (right : F → List O)
    (a : Execution S E A) (b : Execution T F A) : Prop where
  outcome : a.outcome = b.outcome
  state : R a.state b.state
  events : observeEvents left a.events = observeEvents right b.events

theorem related_trans {U G : Type} (R : S → T → Prop) (Q : T → U → Prop)
    (left : E → List O) (middle : F → List O) (right : G → List O)
    (a : Execution S E A) (b : Execution T F A) (c : Execution U G A)
    (ab : Related R left middle a b) (bc : Related Q middle right b c) :
    Related (fun s u => ∃ t, R s t ∧ Q t u) left right a c :=
  ⟨ab.outcome.trans bc.outcome,⟨b.state,ab.state,bc.state⟩,ab.events.trans bc.events⟩

theorem related_follow (R : S → T → Prop) (left : E → List O) (right : F → List O)
    (a : Execution S E A) (b : Execution T F A) (hr : Related R left right a b)
    (f : A → S → Execution S E B) (g : A → T → Execution T F B)
    (next : ∀ v s t, R s t → Related R left right (f v s) (g v t)) :
    Related R left right (a.follow f) (b.follow g) := by
  rcases a with ⟨ao,as,ae⟩
  rcases b with ⟨bo,bs,be⟩
  rcases hr with ⟨ho,hs,he⟩
  dsimp at ho hs he
  subst bo
  cases ao with
  | stopped why => exact ⟨rfl,hs,he⟩
  | returned v =>
    obtain ⟨hn,ht,hv⟩ := next v as bs hs
    refine ⟨hn,ht,?_⟩
    change observeEvents left (ae ++ (f v as).events) =
      observeEvents right (be ++ (g v bs).events)
    rw [observe_append, observe_append, he, hv]

def HandlerRelated (R : S → T → Prop) (left : E → List O) (right : F → List O)
    (h : Handler I S E) (g : Handler I T F) : Prop :=
  ∀ o s t, R s t → Related R left right (h o s) (g o t)

/-- Lift interpreted per-operation laws through well-founded, value-adaptive contexts.
    The context obtains replies only; it cannot inspect hidden handler state. -/
theorem run_related (R : S → T → Prop) (left : E → List O) (right : F → List O)
    (h : Handler I S E) (g : Handler I T F)
    (law : HandlerRelated R left right h g)
    (p : Proc I A) (s : S) (t : T) (initial : R s t) :
    Related R left right (p.run h s) (p.run g t) := by
  induction p generalizing s t with
  | done a => exact ⟨rfl,initial,rfl⟩
  | halt why => exact ⟨rfl,initial,rfl⟩
  | call o k ih =>
    exact related_follow R left right _ _ (law o s t initial) _ _ ih

/-- A final-state observer is permitted only when the residual relation supports it. -/
theorem related_observer {V : Type} (R : S → T → Prop)
    (left : E → List O) (right : F → List O)
    (stateLeft : S → V) (stateRight : T → V)
    (compatible : ∀ s t, R s t → stateLeft s = stateRight t)
    (a : Execution S E A) (b : Execution T F A) (hr : Related R left right a b) :
    (a.outcome, stateLeft a.state, observeEvents left a.events) =
    (b.outcome, stateRight b.state, observeEvents right b.events) := by
  rw [hr.outcome, compatible _ _ hr.state, hr.events]

/-- A semantic contract describes the actual whole result, including failure post-state. -/
structure Contract (S E A : Type) where
  pre : S → Prop
  post : S → Execution S E A → Prop

def Satisfies (c : Contract S E A) (f : S → Execution S E A) : Prop :=
  ∀ s, c.pre s → c.post s (f s)

/-- Facts are interpreted predicates on state, separate from syntax-level summaries. -/
theorem frame_transfer {Fact : Type} (means : Fact → S → Prop)
    (c : Contract S E A) (f : S → Execution S E A) (law : Satisfies c f)
    (kept : Fact → Prop)
    (frame : ∀ s r, c.post s r → ∀ fact, kept fact → means fact s → means fact r.state)
    (s : S) (legal : c.pre s) (fact : Fact) (keep : kept fact) (old : means fact s) :
    means fact (f s).state := frame s (f s) (law s legal) fact keep old

end PIR
