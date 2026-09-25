import Zkc.Semantics.InterpretationAdmission
import Zkc.Semantics.MonadExecution

/-! Iteration of finite effectful bodies. The approximation index is proof or
scheduling fuel, not a deployment limit. Handler state and emitted events survive
every continuation and terminal stop. Stored-source admission and native capacity
are separate obligations; a host function alone is not a compiler representation. -/

set_option autoImplicit false

namespace PIR.Iteration

variable {I J : Signature} {C A S T E F O : Type}

/-- A finite prefix of an outer iteration. `inl` is a pending continuation,
not a logical stop. The body remains an inspectable finite process. -/
def approximate (body : C → Proc I (C ⊕ A)) : Nat → C → Proc I (C ⊕ A)
  | 0, seed => .done (.inl seed)
  | n + 1, seed => (body seed).bind fun
      | .inl next => approximate body n next
      | .inr value => .done (.inr value)

def resume (body : C → Proc I (C ⊕ A)) (fuel : Nat) : C ⊕ A → Proc I (C ⊕ A)
  | .inl next => approximate body fuel next
  | .inr value => .done (.inr value)

theorem approximate_add (body : C → Proc I (C ⊕ A)) (n m : Nat) (seed : C) :
    approximate body (n + m) seed = (approximate body n seed).bind (resume body m) := by
  induction n generalizing seed with
  | zero => simp [approximate, resume, Proc.bind]
  | succ n ih =>
    simp only [Nat.succ_add, approximate, Proc.bind_assoc]
    congr 1
    funext answer
    cases answer with
    | inl next => exact ih next
    | inr value => rfl

def evaluate (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (fuel : Nat) (seed : C) (state : S) : Execution S E (C ⊕ A) :=
  (approximate body fuel seed).run handler state

/-- Interpret actual finite prefixes in a selected monad. A probabilistic
handler must separately justify its distribution and retain the joint state;
outer failure is not converted to an inner execution stop. State in the outer
monad is threaded by bind, not saved inside the returned Execution record. -/
def evaluateM {m : Type → Type} [Monad m] (body : C → Proc I (C ⊕ A))
    (handler : MonadHandler m I S E) (fuel : Nat) (seed : C) (state : S) :
    m (Execution S E (C ⊕ A)) :=
  (approximate body fuel seed).runM handler state

theorem evaluateM_add {m : Type → Type} [Monad m] [LawfulMonad m]
    (body : C → Proc I (C ⊕ A)) (handler : MonadHandler m I S E)
    (n k : Nat) (seed : C) (state : S) :
    evaluateM body handler (n + k) seed state =
      (evaluateM body handler n seed state >>= fun result =>
        result.followM (fun answer => (resume body k answer).runM handler)) := by
  simp only [evaluateM, approximate_add, runM_bind]

theorem evaluateM_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (fuel : Nat) (seed : C) (state : S) :
    evaluateM (m := m) body (fun op s => pure (handler op s)) fuel seed state =
      pure (evaluate body handler fuel seed state) :=
  runM_pure handler _ state

theorem evaluate_add (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (n m : Nat) (seed : C) (state : S) :
    evaluate body handler (n + m) seed state =
      (evaluate body handler n seed state).follow
        (fun answer residual => (resume body m answer).run handler residual) := by
  simp only [evaluate, approximate_add, run_bind]

/-- Grouping `width` source steps into one controller step preserves the
finite process at the translated horizon. An unchanged deployment cap would
describe a different policy. Zero-width groups make no source progress. -/
theorem approximate_blocks (body : C → Proc I (C ⊕ A))
    (width blocks : Nat) (seed : C) :
    approximate (fun c => approximate body width c) blocks seed =
      approximate body (blocks * width) seed := by
  induction blocks generalizing seed with
  | zero => simp only [Nat.zero_mul, approximate]
  | succ blocks ih =>
    conv => rhs; rw [Nat.succ_mul, Nat.add_comm, approximate_add]
    simp only [approximate]
    congr 1
    funext answer
    cases answer with
    | inl next => exact ih next
    | inr value => rfl

/-- A fatal stop finishes the controller as surely as a produced result. -/
def Finished (result : Execution S E (C ⊕ A)) : Prop :=
  match result.outcome with
  | .returned (.inl _) => False
  | .returned (.inr _) | .stopped _ => True

theorem finished_stable (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (n m : Nat) (seed : C) (state : S)
    (finished : Finished (evaluate body handler n seed state)) :
    evaluate body handler (n + m) seed state = evaluate body handler n seed state := by
  rw [evaluate_add]
  generalize evaluate body handler n seed state = result at *
  rcases result with ⟨outcome, residual, events⟩
  cases outcome with
  | stopped why => rfl
  | returned answer =>
    cases answer with
    | inl next => exact False.elim finished
    | inr value => simp [Execution.follow, resume, Proc.run]

/-- A selected deployment cap turns only an unfinished result into exhaustion.
No further work or events are fabricated at this boundary. Accounting that must
distinguish pending from a body's own exhaustion uses the unclosed prefix. -/
def close (result : Execution S E (C ⊕ A)) : Execution S E A :=
  { result with outcome := match result.outcome with
    | .returned (.inl _) => .stopped .exhausted
    | .returned (.inr value) => .returned value
    | .stopped reason => .stopped reason }

@[simp] theorem close_state (result : Execution S E (C ⊕ A)) :
    (close result).state = result.state := rfl

@[simp] theorem close_events (result : Execution S E (C ⊕ A)) :
    (close result).events = result.events := rfl

/-- All finite prefixes remain pending. Their states and event prefixes are
still supplied by `evaluate`; divergent executions are not an erased `none`. -/
def Diverges (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (seed : C) (state : S) : Prop :=
  ∀ fuel, ¬ Finished (evaluate body handler fuel seed state)

def Terminates (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (seed : C) (state : S) : Prop :=
  ∃ fuel, Finished (evaluate body handler fuel seed state)

theorem diverges_iff_not_terminates (body : C → Proc I (C ⊕ A))
    (handler : Handler I S E) (seed : C) (state : S) :
    Diverges body handler seed state ↔ ¬ Terminates body handler seed state := by
  simp [Diverges, Terminates]

theorem finished_unique (body : C → Proc I (C ⊕ A)) (handler : Handler I S E)
    (n m : Nat) (seed : C) (state : S)
    (left : Finished (evaluate body handler n seed state))
    (right : Finished (evaluate body handler m seed state)) :
    evaluate body handler n seed state = evaluate body handler m seed state := by
  rw [← finished_stable body handler n m seed state left,
    Nat.add_comm n m, finished_stable body handler m n seed state right]

theorem interpret_approximate (body : C → Proc I (C ⊕ A))
    (operations : OperationInterpretation I J) (fuel : Nat) (seed : C) :
    (approximate body fuel seed).interpret operations =
      approximate (fun c => (body c).interpret operations) fuel seed := by
  induction fuel generalizing seed with
  | zero => rfl
  | succ n ih =>
    simp only [approximate, Proc.interpret_bind]
    congr 1
    funext answer
    cases answer with
    | inl next => exact ih next
    | inr value => rfl

theorem within_approximate (body : C → Proc I (C ⊕ A))
    (bound : Nat) (bounded : ∀ seed, Within bound (body seed))
    (fuel : Nat) (seed : C) : Within (fuel * bound) (approximate body fuel seed) := by
  induction fuel generalizing seed with
  | zero => simp [approximate, Within]
  | succ n ih =>
    simp only [approximate, Nat.succ_mul]
    rw [Nat.add_comm]
    apply Boundary.within_bind _ _ bound (n * bound) (bounded seed)
    intro answer
    cases answer with
    | inl next => exact ih next
    | inr value => cases n * bound <;> trivial

/-- The invariant links each continuation to its actual entry phase. Returning
from a body must either reestablish it or satisfy the terminal postcondition. -/
theorem approximate_admission (body : C → Proc I (C ⊕ A))
    (interaction : Interaction I) (invariant : C → interaction.Phase → Prop)
    (post : A → interaction.Phase → Prop)
    (formed : ∀ seed phase, invariant seed phase → Conforms interaction (body seed) phase)
    (exits : ∀ seed phase, invariant seed phase →
      Boundary.Returns interaction (fun answer phase =>
        match answer with | .inl next => invariant next phase | .inr value => post value phase)
        (body seed) phase)
    (fuel : Nat) (seed : C) (phase : interaction.Phase) (initial : invariant seed phase) :
    Conforms interaction (approximate body fuel seed) phase ∧
      Boundary.Returns interaction (fun answer phase =>
        match answer with | .inl next => invariant next phase | .inr value => post value phase)
        (approximate body fuel seed) phase := by
  induction fuel generalizing seed phase with
  | zero => exact ⟨trivial, initial⟩
  | succ n ih =>
    constructor
    · apply Boundary.conforms_bind interaction (body seed) _ _ phase
        (formed seed phase initial) (exits seed phase initial)
      intro answer last legal
      cases answer with
      | inl next => exact (ih next last legal).1
      | inr value => trivial
    · apply Boundary.returns_bind interaction (body seed) _ _ _ phase (exits seed phase initial)
      intro answer last legal
      cases answer with
      | inl next => exact (ih next last legal).2
      | inr value => exact legal

/-- Bound admitted continuations only. The invariant is preserved on every
typed returning branch, not merely on the replies of one chosen handler. -/
theorem within_approximate_of_invariant (body : C → Proc I (C ⊕ A))
    (interaction : Interaction I) (invariant : C → interaction.Phase → Prop)
    (post : A → interaction.Phase → Prop) (bound : Nat)
    (bounded : ∀ seed phase, invariant seed phase → Within bound (body seed))
    (exits : ∀ seed phase, invariant seed phase →
      Boundary.Returns interaction (fun answer phase =>
        match answer with | .inl next => invariant next phase | .inr value => post value phase)
        (body seed) phase)
    (fuel : Nat) (seed : C) (phase : interaction.Phase) (initial : invariant seed phase) :
    Within (fuel * bound) (approximate body fuel seed) := by
  induction fuel generalizing seed phase with
  | zero => simp [approximate, Within]
  | succ fuel ih =>
    rw [Nat.succ_mul, Nat.add_comm]
    apply Boundary.within_bind_of_returns interaction (body seed) _ _ phase bound (fuel * bound)
      (bounded seed phase initial) (exits seed phase initial)
    intro answer last legal
    cases answer with
    | inl next => exact ih next last legal
    | inr value => cases fuel * bound <;> trivial

/-- Per-attempt simulation lifts through every prefix, passing the actual
residual state between attempts and retaining stopped effects. -/
theorem evaluate_related (body : C → Proc I (C ⊕ A))
    (other : C → Proc J (C ⊕ A)) (left : Handler I S E) (right : Handler J T F)
    (relation : S → T → Prop) (viewLeft : E → List O) (viewRight : F → List O)
    (law : ∀ seed s t, relation s t →
      Related relation viewLeft viewRight ((body seed).run left s) ((other seed).run right t))
    (fuel : Nat) (seed : C) (s : S) (t : T) (initial : relation s t) :
    Related relation viewLeft viewRight
      (evaluate body left fuel seed s) (evaluate other right fuel seed t) := by
  induction fuel generalizing seed s t with
  | zero => exact ⟨rfl, initial, rfl⟩
  | succ n ih =>
    simp only [evaluate, approximate, run_bind]
    apply related_follow relation viewLeft viewRight _ _ (law seed s t initial)
    intro answer s t related
    cases answer with
    | inl next => exact ih next s t related
    | inr value => exact ⟨rfl, related, rfl⟩

end PIR.Iteration
