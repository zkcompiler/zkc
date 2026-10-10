import Zkc.Semantics.ExecutionPath

set_option autoImplicit false
namespace PIR.Boundary
variable {I : Signature} {A B S E : Type}

/-- A returned value's phase postcondition, quantified over all typed replies.
    Stops have no returning continuation; they remain observable in Execution. -/
def Returns (P : Interaction I) (post : A → P.Phase → Prop) :
    Proc I A → P.Phase → Prop
  | .done a, phase => post a phase
  | .halt _, _ => True
  | .call o k, phase => ∀ a, Returns P post (k a) (P.advance phase o a)

theorem returns_mono (P : Interaction I) (p : Proc I A)
    (post out : A → P.Phase → Prop) (phase : P.Phase)
    (exits : Returns P post p phase)
    (implies : ∀ value finalPhase, post value finalPhase → out value finalPhase) :
    Returns P out p phase := by
  induction p generalizing phase with
  | done value => exact implies value phase exits
  | halt why => trivial
  | call op next ih => exact fun reply => ih reply _ (exits reply)

/-- The missing premise of phase-safe sequencing is the first body's exit,
    not its conformance at some unrelated initial phase. -/
theorem conforms_bind (P : Interaction I) (p : Proc I A) (k : A → Proc I B)
    (post : A → P.Phase → Prop) (phase : P.Phase)
    (formed : Conforms P p phase) (exits : Returns P post p phase)
    (next : ∀ a phase, post a phase → Conforms P (k a) phase) :
    Conforms P (p.bind k) phase := by
  induction p generalizing phase with
  | done a => exact next a phase exits
  | halt why => trivial
  | call o cont ih =>
    exact ⟨formed.1, fun a => ih a _ (formed.2 a) (exits a)⟩

theorem returns_bind (P : Interaction I) (p : Proc I A) (k : A → Proc I B)
    (post : A → P.Phase → Prop) (out : B → P.Phase → Prop) (phase : P.Phase)
    (exits : Returns P post p phase)
    (next : ∀ a phase, post a phase → Returns P out (k a) phase) :
    Returns P out (p.bind k) phase := by
  induction p generalizing phase with
  | done a => exact next a phase exits
  | halt why => trivial
  | call o cont ih => exact fun a => ih a _ (exits a)

/-- Postconditions refer to the actual instrumented execution's final phase. -/
theorem actual_return (P : Interaction I) (p : Proc I A) (h : Handler I S E)
    (post : A → P.Phase → Prop) (phase : P.Phase) (s : S)
    (exits : Returns P post p phase) (a : A)
    (returned : (p.run (ExecutionPath.handler P h) (phase,s)).outcome = .returned a) :
    post a (p.run (ExecutionPath.handler P h) (phase,s)).state.1 := by
  induction p generalizing phase s with
  | done value =>
    cases returned
    exact exits
  | halt why => cases returned
  | call o k ih =>
    simp only [Proc.run, ExecutionPath.handler] at returned ⊢
    cases hx : h o s with
    | mk outcome t es =>
      cases outcome with
      | stopped why => simp [hx, Execution.follow] at returned
      | returned reply =>
        simp only [hx, Execution.follow] at returned ⊢
        exact ih reply _ t (exits reply) returned

theorem within_mono (p : Proc I A) (n m : Nat) (le : n ≤ m)
    (bound : Within n p) : Within m p := by
  induction p generalizing n m with
  | done => cases m <;> trivial
  | halt => cases m <;> trivial
  | call o k ih =>
    cases n with
    | zero => exact False.elim bound
    | succ n =>
      cases m with
      | zero => omega
      | succ m => exact fun a => ih a n m (by omega) (bound a)

theorem within_bind (p : Proc I A) (k : A → Proc I B) (n m : Nat)
    (first : Within n p) (next : ∀ a, Within m (k a)) :
    Within (n+m) (p.bind k) := by
  induction p generalizing n with
  | done a => exact within_mono _ m (n+m) (by omega) (next a)
  | halt => cases n+m <;> trivial
  | call o cont ih =>
    cases n with
    | zero => exact False.elim first
    | succ n =>
      rw [Nat.succ_add]
      exact fun a => ih a n (first a)

/-- A suffix bound is needed only at returns certified by the prefix, at
their actual logical phase. This retains value-dependent invariants instead
of requiring a bound for unreachable continuation values. -/
theorem within_bind_of_returns (P : Interaction I) (p : Proc I A)
    (k : A → Proc I B) (post : A → P.Phase → Prop) (phase : P.Phase) (n m : Nat)
    (first : Within n p) (exits : Returns P post p phase)
    (next : ∀ a phase, post a phase → Within m (k a)) :
    Within (n + m) (p.bind k) := by
  induction p generalizing n phase with
  | done a => exact within_mono _ m (n + m) (by omega) (next a phase exits)
  | halt => cases n + m <;> trivial
  | call o cont ih =>
    cases n with
    | zero => exact False.elim first
    | succ n =>
      rw [Nat.succ_add]
      exact fun a => ih a _ _ (first a) (exits a)

theorem repeat_bound (step : A → Proc I A) (m : Nat) (bound : ∀ a, Within m (step a))
    (n : Nat) (a : A) : Within (n*m) (repeatN n step a) := by
  induction n generalizing a with
  | zero => simp [repeatN, Within]
  | succ n ih =>
    simpa only [repeatN, Nat.succ_mul, Nat.add_comm] using
      within_bind (step a) (repeatN n step) m (n*m) (bound a) ih

/-- Public finite repetition carries an invariant across actual return edges. -/
theorem repeat_formed (P : Interaction I) (step : A → Proc I A)
    (inv : A → P.Phase → Prop)
    (body : ∀ a phase, inv a phase → Conforms P (step a) phase)
    (preserve : ∀ a phase, inv a phase → Returns P inv (step a) phase)
    (n : Nat) (a : A) (phase : P.Phase) (initial : inv a phase) :
    Conforms P (repeatN n step a) phase ∧ Returns P inv (repeatN n step a) phase := by
  induction n generalizing a phase with
  | zero => exact ⟨trivial,initial⟩
  | succ n ih =>
    exact ⟨conforms_bind P _ _ inv phase (body a phase initial)
      (preserve a phase initial) (fun a phase h => (ih a phase h).1),
      returns_bind P _ _ inv inv phase (preserve a phase initial)
        (fun a phase h => (ih a phase h).2)⟩

end PIR.Boundary
