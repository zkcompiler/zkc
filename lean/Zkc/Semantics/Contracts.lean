import Zkc.Semantics.Execution

set_option autoImplicit false

namespace PIR

variable {I : Signature} {S E A B : Type}

/-- Contract consequence keeps the implementation fixed and changes the claim.
    The new precondition must imply the established one. -/
theorem satisfies_consequence (c d : Contract S E A)
    (f : S → Execution S E A) (law : Satisfies c f)
    (pre : ∀ s, d.pre s → c.pre s)
    (post : ∀ s r, d.pre s → c.post s r → d.post s r) :
    Satisfies d f := by
  intro s admissible
  exact post s (f s) admissible (law s (pre s admissible))

/-- Compose contracts over the entire first execution. A returned error is
    still a reply and must meet its continuation's precondition. A terminal
    stop retains its exact state and events without calling that continuation.
    The universal precondition is conservative over every result allowed by c. -/
def Contract.seq (c : Contract S E A) (d : A → Contract S E B) : Contract S E B where
  pre s := c.pre s ∧ ∀ first, c.post s first →
    ∀ a, first.outcome = .returned a → (d a).pre first.state
  post s out := ∃ first, c.post s first ∧
    match first.outcome with
    | .stopped why => out = ⟨.stopped why, first.state, first.events⟩
    | .returned a => ∃ last, (d a).post first.state last ∧
        out = ⟨last.outcome, last.state, first.events ++ last.events⟩

theorem satisfies_then (c : Contract S E A) (d : A → Contract S E B)
    (f : S → Execution S E A) (g : A → S → Execution S E B)
    (firstLaw : Satisfies c f) (nextLaw : ∀ a, Satisfies (d a) (g a)) :
    Satisfies (c.seq d) (fun s => (f s).follow g) := by
  intro s admissible
  have firstPost := firstLaw s admissible.1
  refine ⟨f s, firstPost, ?_⟩
  cases outcome : (f s).outcome with
  | stopped why => simp [outcome, Execution.follow]
  | returned a =>
    exact ⟨g a (f s).state,
      nextLaw a (f s).state (admissible.2 (f s) firstPost a outcome),
      by simp [Execution.follow, outcome]⟩

/-- The contract rule is about the same sequencing interpreted by Proc.bind. -/
theorem satisfies_bind (h : Handler I S E) (p : Proc I A) (k : A → Proc I B)
    (c : Contract S E A) (d : A → Contract S E B)
    (firstLaw : Satisfies c (p.run h))
    (nextLaw : ∀ a, Satisfies (d a) ((k a).run h)) :
    Satisfies (c.seq d) ((p.bind k).run h) := by
  intro s admissible
  rw [run_bind]
  exact satisfies_then c d (p.run h) (fun a => (k a).run h)
    firstLaw nextLaw s admissible

end PIR
