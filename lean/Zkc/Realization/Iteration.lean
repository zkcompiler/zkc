import Zkc.Semantics.Iteration
import Zkc.Realization.Simulation

/-! Iteration with represented continuation and result values. Relations are
interpreted in the actual post-states, including pending prefixes. The two
controllers advance in lockstep; changing the step unit needs another law. -/

set_option autoImplicit false
namespace Zkc.Realization.Iteration
open PIR
variable {I J : Signature} {C D A B S T E F O : Type}

/-- Pending and completed returns must agree on their tag; their payloads may
use different representations. A continuation relation can include the
invariant required by the next body. -/
def ResultRel (continuations : C → S → D → T → Prop)
    (results : A → S → B → T → Prop) : (C ⊕ A) → S → (D ⊕ B) → T → Prop
  | .inl c, s, .inl d, t => continuations c s d t
  | .inr a, s, .inr b, t => results a s b t
  | _, _, _, _ => False

/-- Complete per-body correspondence lifts from related continuations, rather
than requiring equal continuation values or equal representation types. -/
theorem evaluate_relates (body : C → Proc I (C ⊕ A))
    (other : D → Proc J (D ⊕ B)) (left : Handler I S E) (right : Handler J T F)
    (states : S → T → Prop) (continuations : C → S → D → T → Prop)
    (results : A → S → B → T → Prop) (viewLeft : E → List O) (viewRight : F → List O)
    (law : ∀ c s d t, states s t → continuations c s d t →
      Execution.Relates states (ResultRel continuations results) viewLeft viewRight
        ((body c).run left s) ((other d).run right t))
    (fuel : Nat) (c : C) (s : S) (d : D) (t : T)
    (initial : states s t) (seed : continuations c s d t) :
    Execution.Relates states (ResultRel continuations results) viewLeft viewRight
      (PIR.Iteration.evaluate body left fuel c s)
      (PIR.Iteration.evaluate other right fuel d t) := by
  induction fuel generalizing c s d t with
  | zero => exact ⟨seed, initial, rfl⟩
  | succ fuel ih =>
    simp only [PIR.Iteration.evaluate, PIR.Iteration.approximate, run_bind]
    apply Execution.Relates.follow states (ResultRel continuations results)
      (ResultRel continuations results) viewLeft viewRight _ _ (law c s d t initial seed)
    intro answer s answer' t related values
    cases answer <;> cases answer' <;> simp only [ResultRel] at values
    · exact ih _ _ _ _ related values
    · exact ⟨values, related, rfl⟩

/-- Closing matching pending prefixes preserves exact exhaustion, state and
events. Finished values retain their state-dependent representation law. -/
theorem close_relates (states : S → T → Prop)
    (continuations : C → S → D → T → Prop) (results : A → S → B → T → Prop)
    (viewLeft : E → List O) (viewRight : F → List O)
    (source : Execution S E (C ⊕ A)) (target : Execution T F (D ⊕ B))
    (related : Execution.Relates states (ResultRel continuations results)
      viewLeft viewRight source target) :
    Execution.Relates states results viewLeft viewRight
      (PIR.Iteration.close source) (PIR.Iteration.close target) := by
  refine ⟨?_, related.state, related.events⟩
  have h := related.outcome
  cases hs : source.outcome <;> cases ht : target.outcome <;>
    simp only [hs, ht, Outcome.Relates] at h
  · rename_i a b
    cases a <;> cases b <;>
      simp_all [PIR.Iteration.close, Outcome.Relates, ResultRel]
  · simpa [PIR.Iteration.close, hs, ht, Outcome.Relates] using h

end Zkc.Realization.Iteration
