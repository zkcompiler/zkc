module

public import Zkc.Semantics.MonadExecution
public import VCVio.ProgramLogic.Relational.Basic

@[expose] public section

/-! Local probabilistic handler refinement for the existing process semantics.

VCVio owns the probability logic. The postcondition is the existing
`PIR.Related`: equal returned values or stop reasons, related residual states,
and equal ordered observations. The state relation may connect different
representations and includes any shared mutable service/adversary state.
-/

namespace ZkcSecurity.VCVio.Coupling

open OracleComp OracleComp.ProgramLogic.Relational

variable {I : PIR.Signature} {S T E F O A B : Type}

/-- Sequence related records. Stopped records retain their state and observed
prefix without invoking either continuation. -/
theorem followM_relTriple (R : S → T → Prop)
    (left : E → List O) (right : F → List O)
    (a : PIR.Execution S E A) (b : PIR.Execution T F A)
    (related : PIR.Related R left right a b)
    (f : A → S → ProbComp (PIR.Execution S E B))
    (g : A → T → ProbComp (PIR.Execution T F B))
    (next : ∀ value s t, R s t →
      RelTriple (f value s) (g value t) (PIR.Related R left right)) :
    RelTriple (a.followM f) (b.followM g) (PIR.Related R left right) := by
  rcases a with ⟨ao, s, es⟩
  rcases b with ⟨bo, t, fs⟩
  rcases related with ⟨outcome, state, events⟩
  dsimp at outcome state events
  subst bo
  cases ao with
  | stopped why => exact relTriple_pure_pure ⟨rfl, state, events⟩
  | returned value =>
      apply relTriple_bind (next value s t state)
      intro a b related
      apply relTriple_pure_pure
      refine ⟨related.outcome, related.state, ?_⟩
      change PIR.observeEvents left (es ++ a.events) =
        PIR.observeEvents right (fs ++ b.events)
      rw [PIR.observe_append, PIR.observe_append, events, related.events]

/-- Per-action couplings lift through every well-founded, reply-adaptive
process. The hypotheses concern only a single handler action at related
states; no coupling of complete runs or continuations is assumed. -/
theorem runM_relTriple (R : S → T → Prop)
    (left : E → List O) (right : F → List O)
    (h : PIR.MonadHandler ProbComp I S E)
    (g : PIR.MonadHandler ProbComp I T F)
    (localLaw : ∀ action s t, R s t →
      RelTriple (h action s) (g action t) (PIR.Related R left right))
    (process : PIR.Proc I A) (s : S) (t : T) (initial : R s t) :
    RelTriple (process.runM h s) (process.runM g t) (PIR.Related R left right) := by
  induction process generalizing s t with
  | done value => exact relTriple_pure_pure ⟨rfl, initial, rfl⟩
  | halt why => exact relTriple_pure_pure ⟨rfl, initial, rfl⟩
  | call action continuation ih =>
      exact relTriple_bind (localLaw action s t initial) fun a b related =>
        followM_relTriple R left right a b related _ _ ih

end ZkcSecurity.VCVio.Coupling
