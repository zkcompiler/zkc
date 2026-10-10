import Zkc.Semantics.MonadExecution
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

namespace PIR.ProductTape

variable {D S E A : Type} {J : Signature}

/-- The only access to provider state is a next-coordinate draw. Local operations
    can be arbitrary stateful probabilistic handlers, but receive no tape. -/
def sig (D : Type) (J : Signature) : Signature :=
  ⟨Option J.Op, fun | none => D | some o => J.Reply o⟩

def localSource (p : Proc J A) : Proc (sig D J) A :=
  match p with
  | .done a => .done a
  | .halt why => .halt why
  | .call o k => .call (some o) (fun x => localSource (k x))

def retainLocal (rest : List D) (r : Execution S E A) : Execution (S × List D) (Sum D E) A :=
  ⟨r.outcome,(r.state,rest),r.events.map Sum.inr⟩

noncomputable def tape (q : PMF D) : Nat → PMF (List D)
  | 0 => pure []
  | n+1 => do
    let d ← q
    let rest ← tape q n
    pure (d::rest)

/-- Distribution of the unconsumed suffix; local state is retained exactly. -/
noncomputable def expand (q : PMF D) (st : S × Nat) : PMF (S × List D) := do
  let rest ← tape q st.2
  pure (st.1,rest)

theorem tape_length (q : PMF D) (n : Nat) (xs : List D)
    (hx : xs ∈ (tape q n).support) : xs.length = n := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := (PMF.mem_support_pure_iff _ _).mp hx
    simp [he]
  | succ n ih =>
    obtain ⟨d,_,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨rest,hr,he⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    have heq : xs = d::rest := (PMF.mem_support_pure_iff _ _).mp he
    subst xs
    simp [ih rest hr]

theorem bind_supported {X Y : Type} (p : PMF X) (f g : X → PMF Y)
    (same : ∀ x ∈ p.support, f x = g x) : p.bind f = p.bind g := by
  apply PMF.ext
  intro y
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · rw [same x hx]

/-- The abstract checkpoint is recoverable from the actual residual state.
    It exposes tape LENGTH, not the hidden suffix values. -/
def checkpoint (r : Execution (S × List D) E A) : Execution (S × Nat) E A :=
  ⟨r.outcome,(r.state.1,r.state.2.length),r.events⟩

theorem checkpoint_expand (q : PMF D) (r : Execution (S × Nat) E A) :
    (Execution.expand (expand q) r >>= fun actual => pure (checkpoint actual)) =
      (pure r : PMF _) := by
  simp only [Execution.expand, expand, bind_assoc, pure_bind, checkpoint]
  apply (bind_supported _ _ (fun _ => pure r) ?_).trans (PMF.bind_const _ _)
  intro xs hx
  rw [tape_length q r.state.2 xs hx]

theorem reconstruct_use {B : Type} (q : PMF D) (r : Execution (S × Nat) E A)
    (f : Execution (S × Nat) E A → Execution (S × List D) E A → PMF B) :
    (Execution.expand (expand q) r >>= fun actual => f (checkpoint actual) actual) =
      (Execution.expand (expand q) r >>= fun actual => f r actual) := by
  simp only [Execution.expand, expand, bind_assoc, pure_bind, checkpoint]
  apply bind_supported
  intro xs hx
  rw [tape_length q r.state.2 xs hx]


noncomputable def persistent (localH : MonadHandler PMF J S E) :
    MonadHandler PMF (sig D J) (S × List D) (Sum D E)
  | none, (s,[]) => pure ⟨.stopped .exhausted,(s,[]),[]⟩
  | none, (s,d::rest) => pure ⟨.returned d,(s,rest),[.inl d]⟩
  | some o, (s,rest) => do
    let r ← localH o s
    pure ⟨r.outcome,(r.state,rest),r.events.map Sum.inr⟩

noncomputable def online (q : PMF D) (localH : MonadHandler PMF J S E) :
    MonadHandler PMF (sig D J) (S × Nat) (Sum D E)
  | none, (s,0) => pure ⟨.stopped .exhausted,(s,0),[]⟩
  | none, (s,n+1) => do
    let d ← q
    pure ⟨.returned d,(s,n),[.inl d]⟩
  | some o, (s,n) => do
    let r ← localH o s
    pure ⟨r.outcome,(r.state,n),r.events.map Sum.inr⟩

/-- Embed a local effect source without granting it access to the provider tape.
    Full local failure post-state and events are preserved. -/
theorem local_source_exact (localH : MonadHandler PMF J S E) (p : Proc J A)
    (s : S) (rest : List D) :
    (localSource p).runM (persistent localH) (s,rest) =
      (p.runM localH s >>= fun r => pure (retainLocal rest r)) := by
  induction p generalizing s with
  | done a => simp [localSource, Proc.runM, retainLocal]
  | halt why => simp [localSource, Proc.runM, retainLocal]
  | call o k ih =>
    simp only [localSource, Proc.runM, persistent, bind_assoc, pure_bind]
    congr 1
    funext r
    rcases r with ⟨out,s,es⟩
    cases out with
    | stopped why => simp [Execution.followM, retainLocal]
    | returned a =>
      simp only [Execution.followM]
      rw [ih]
      simp [retainLocal]

/-- Each concrete pop/local transition maintains the suffix interpretation.
    The local case uses commutation of INDEPENDENT samples, not marginal uniformity. -/
theorem handler_expand (q : PMF D) (localH : MonadHandler PMF J S E)
    (o : (sig D J).Op) (st : S × Nat) :
    (expand q st >>= persistent localH o) =
      (online q localH o st >>= Execution.expand (expand q)) := by
  rcases st with ⟨s,n⟩
  cases o with
  | none =>
    cases n <;> simp [expand, tape, persistent, online, Execution.expand, bind_assoc]
  | some o =>
    simp only [expand, persistent, online, Execution.expand, bind_assoc, pure_bind]
    exact PMF.bind_comm _ _ _

/-- For EVERY finite reply-adaptive program and EVERY tape length, actual eager
    execution equals online execution followed by reconstruction of the residual
    hidden suffix. Stops, exhaustion, local failure state and emissions all survive. -/
theorem execution_expand (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) :
    (expand q st >>= p.runM (persistent localH)) =
      (p.runM (online q localH) st >>= Execution.expand (expand q)) :=
  runM_expand (expand q) (online q localH) (persistent localH)
    (handler_expand q localH) p st

/-- Arbitrary initial setup/local-state correlations are allowed. Conditional
    on that sampled state and length, the provider suffix is the stated product.
    The source may be selected from that entire state, but not from its future tape. -/
theorem initialized_execution (q : PMF D) (localH : MonadHandler PMF J S E)
    (init : PMF (S × Nat)) (source : S × Nat → Proc (sig D J) A) :
    (do
      let st ← init
      let actual ← expand q st
      (source st).runM (persistent localH) actual) =
    (do
      let st ← init
      let r ← (source st).runM (online q localH) st
      Execution.expand (expand q) r) := by
  congr 1
  funext st
  exact execution_expand q localH (source st) st

theorem checkpoint_execution (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) :
    ((expand q st >>= p.runM (persistent localH)) >>= fun actual =>
      pure (checkpoint actual)) = p.runM (online q localH) st := by
  rw [execution_expand, bind_assoc]
  simp_rw [checkpoint_expand]
  exact bind_pure _

theorem outcome_expand {B : Type} (q : PMF D) (r : Execution (S × Nat) E A)
    (f : Outcome A → PMF B) :
    (Execution.expand (expand q) r >>= fun actual => f actual.outcome) = f r.outcome := by
  simp only [Execution.expand, expand, bind_assoc, pure_bind]
  exact PMF.bind_const _ _

end PIR.ProductTape
