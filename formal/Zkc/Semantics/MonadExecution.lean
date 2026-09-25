import Zkc.Semantics.Execution

/-! Execution in a selected outer monad.

An inner `Execution` stop retains its post-state and ordered events, including
those from earlier operations. This guarantee applies when the outer monad
produces an `Execution`. An outer `Except.error`, for example, produces no such
record: a later exception can discard an earlier returned state and event
prefix from the result of `Proc.runM`. This API neither recovers those fields
nor specifies rollback or persistence of effects outside `Execution`.

The laws below equate meanings in the selected monad. They do not imply that
outer exceptions become inner stops, or that a probabilistic interpretation
has total mass. Complete-result and normalization obligations remain separate.
-/

set_option autoImplicit false

namespace PIR

variable {m : Type → Type} [Monad m]
variable {I : Signature} {S T E A B : Type}

abbrev MonadHandler (m : Type → Type) (I : Signature) (S E : Type) :=
  (o : I.Op) → S → m (Execution S E (I.Reply o))

/-- Sequence inside the selected monad. Inner stops retain the execution record;
    an outer effect may produce no record. Probability requires a separate law. -/
def Execution.followM (r : Execution S E A)
    (k : A → S → m (Execution S E B)) : m (Execution S E B) :=
  match r.outcome with
  | .stopped why => pure ⟨.stopped why, r.state, r.events⟩
  | .returned a => do
    let tail ← k a r.state
    pure ⟨tail.outcome, tail.state, r.events ++ tail.events⟩

def Proc.runM (h : MonadHandler m I S E) : Proc I A → S → m (Execution S E A)
  | .done a, s => pure ⟨.returned a, s, []⟩
  | .halt why, s => pure ⟨.stopped why, s, []⟩
  | .call o k, s => do
    let r ← h o s
    r.followM (fun a => (k a).runM h)

theorem followM_lift {n : Type → Type} [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] (r : Execution S E A)
    (k : A → S → m (Execution S E B)) :
    (liftM (r.followM k) : n _) = r.followM (fun a s => liftM (k a s)) := by
  rcases r with ⟨out,s,es⟩
  cases out <;> simp only [Execution.followM, monadLift_bind, monadLift_pure]

theorem runM_lift {n : Type → Type} [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] (h : MonadHandler m I S E) (p : Proc I A) (s : S) :
    (liftM (p.runM h s) : n _) = p.runM (fun o s => liftM (h o s)) s := by
  induction p generalizing s with
  | done a => simp only [Proc.runM, monadLift_pure]
  | halt why => simp only [Proc.runM, monadLift_pure]
  | call o k ih =>
    simp only [Proc.runM, monadLift_bind, followM_lift]
    have hk : (fun a s => (liftM ((k a).runM h s) : n _)) =
        (fun a s => (k a).runM (fun o s => liftM (h o s)) s) :=
      funext fun a => funext (ih a)
    rw [hk]

variable [LawfulMonad m]

theorem followM_pure (r : Execution S E A) (k : A → S → Execution S E B) :
    r.followM (m := m) (fun a s => pure (k a s)) = pure (r.follow k) := by
  cases r with | mk out s es => cases out <;> simp [Execution.followM, Execution.follow]

/-- The deterministic semantics embeds exactly; it is not a second state machine. -/
theorem runM_pure (h : Handler I S E) (p : Proc I A) (s : S) :
    p.runM (m := m) (fun o s => pure (h o s)) s = pure (p.run h s) := by
  induction p generalizing s with
  | done a => rfl
  | halt why => rfl
  | call o k ih =>
    simp only [Proc.runM, Proc.run, pure_bind]
    have hk : (fun a => (k a).runM (m := m) (fun o s => pure (h o s))) =
        (fun a s => pure ((k a).run h s)) := funext fun a => funext (ih a)
    rw [hk]
    exact followM_pure _ _

theorem followM_assoc {C : Type} (r : Execution S E A)
    (f : A → S → m (Execution S E B)) (g : B → S → m (Execution S E C)) :
    (r.followM f >>= fun t => t.followM g) =
      r.followM (fun a s => f a s >>= fun t => t.followM g) := by
  rcases r with ⟨out,s,es⟩
  cases out with
  | stopped why => simp [Execution.followM]
  | returned a =>
    simp only [Execution.followM, bind_assoc, pure_bind]
    congr 1
    funext t
    rcases t with ⟨out,t,fs⟩
    cases out with
    | stopped why => simp
    | returned b => simp [List.append_assoc]

theorem runM_bind (h : MonadHandler m I S E) (p : Proc I A)
    (k : A → Proc I B) (s : S) :
    (p.bind k).runM h s =
      (p.runM h s >>= fun r => r.followM (fun a => (k a).runM h)) := by
  induction p generalizing s with
  | done a => simp [Proc.bind, Proc.runM, Execution.followM]
  | halt why => simp [Proc.bind, Proc.runM, Execution.followM]
  | call o next ih =>
    simp only [Proc.bind, Proc.runM, bind_assoc]
    congr 1
    funext r
    rw [followM_assoc]
    congr 1
    funext a t
    exact ih a t

/-- Interpret hidden residual state by a distribution, preserving every outcome/event. -/
def Execution.expand (η : S → m T) (r : Execution S E A) : m (Execution T E A) := do
  let t ← η r.state
  pure ⟨r.outcome,t,r.events⟩

/-- A local distributional state interpretation lifts through every finite adaptive tree.
    The context sees replies, never the hidden state supplied by η. -/
theorem runM_expand (η : S → m T) (h : MonadHandler m I S E)
    (g : MonadHandler m I T E)
    (law : ∀ o s, (η s >>= g o) = (h o s >>= Execution.expand η))
    (p : Proc I A) (s : S) :
    (η s >>= p.runM g) = (p.runM h s >>= Execution.expand η) := by
  induction p generalizing s with
  | done a => simp [Proc.runM, Execution.expand]
  | halt why => simp [Proc.runM, Execution.expand]
  | call o k ih =>
    simp only [Proc.runM]
    rw [← bind_assoc, law, bind_assoc, bind_assoc]
    congr 1
    funext r
    rcases r with ⟨out,s,es⟩
    cases out with
    | stopped why => simp [Execution.expand, Execution.followM]
    | returned a =>
      simp only [Execution.expand, Execution.followM, bind_assoc, pure_bind]
      rw [← bind_assoc, ih, bind_assoc]
      simp [Execution.expand]

end PIR
