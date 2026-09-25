import Zkc.Semantics.Execution

/-! Relations between complete executions with different value representations.

A returned handle is interpreted in the final native state. Keeping the value
relation state-dependent is necessary for buffers, registries and allocated
results. Stops retain their exact reason, residual state and observations.
These laws relate terminating executions; native progress remains an obligation.
-/

namespace PIR

variable {S T U E F G O A B C D : Type}

namespace Outcome

/-- Lift a return-value relation, preserving every terminal stop exactly. -/
def Relates (values : A → B → Prop) : Outcome A → Outcome B → Prop
  | .returned a, .returned b => values a b
  | .stopped a, .stopped b => a = b
  | _, _ => False

end Outcome

namespace Execution

/-- Representation correspondence at the actual final states. -/
structure Relates (states : S → T → Prop)
    (values : A → S → B → T → Prop)
    (left : E → List O) (right : F → List O)
    (source : Execution S E A) (target : Execution T F B) : Prop where
  outcome : Outcome.Relates (fun a b => values a source.state b target.state)
    source.outcome target.outcome
  state : states source.state target.state
  events : observeEvents left source.events = observeEvents right target.events

/-- Sequencing uses related replies in their related post-states, including
recoverable errors. A terminal stop does not execute either continuation. -/
theorem Relates.follow (states : S → T → Prop)
    (values : A → S → B → T → Prop) (results : C → S → D → T → Prop)
    (left : E → List O) (right : F → List O)
    (source : Execution S E A) (target : Execution T F B)
    (related : Relates states values left right source target)
    (sourceNext : A → S → Execution S E C)
    (targetNext : B → T → Execution T F D)
    (next : ∀ a s b t, states s t → values a s b t →
      Relates states results left right (sourceNext a s) (targetNext b t)) :
    Relates states results left right
      (source.follow sourceNext) (target.follow targetNext) := by
  rcases source with ⟨so, ss, se⟩
  rcases target with ⟨to, ts, te⟩
  rcases related with ⟨ho, hs, he⟩
  cases so with
  | stopped why =>
    cases to with
    | returned b => exact False.elim ho
    | stopped other =>
      exact ⟨ho, hs, he⟩
  | returned a =>
    cases to with
    | stopped why => exact False.elim ho
    | returned b =>
      obtain ⟨hn, ht, hv⟩ := next a ss b ts hs ho
      refine ⟨hn, ht, ?_⟩
      change observeEvents left (se ++ (sourceNext a ss).events) =
        observeEvents right (te ++ (targetNext b ts).events)
      rw [observe_append, observe_append, he, hv]

/-- Compose through the actual middle execution. The resulting state and value
relations separately retain existential middle-state witnesses; the conclusion
does not identify witnesses recovered from those two projections. -/
theorem Relates.trans (states : S → T → Prop) (moreStates : T → U → Prop)
    (values : A → S → B → T → Prop) (moreValues : B → T → C → U → Prop)
    (left : E → List O) (middle : F → List O) (right : G → List O)
    (source : Execution S E A) (target : Execution T F B)
    (final : Execution U G C)
    (first : Relates states values left middle source target)
    (second : Relates moreStates moreValues middle right target final) :
    Relates (fun s u => ∃ t, states s t ∧ moreStates t u)
      (fun a s c u => ∃ t b, states s t ∧ moreStates t u ∧
        values a s b t ∧ moreValues b t c u)
      left right source final := by
  refine ⟨?_, ⟨target.state, first.state, second.state⟩,
    first.events.trans second.events⟩
  have hf := first.outcome
  have hs := second.outcome
  cases so : source.outcome <;> cases to : target.outcome <;>
    cases fo : final.outcome <;>
    simp only [so, to, fo, Outcome.Relates] at hf hs ⊢
  · exact ⟨target.state, _, first.state, second.state, hf, hs⟩
  all_goals first | contradiction | exact hf.trans hs

/-- Existing equal-reply simulations embed without changing their premises. -/
theorem Relates.of_related (states : S → T → Prop)
    (left : E → List O) (right : F → List O)
    (source : Execution S E A) (target : Execution T F A)
    (related : PIR.Related states left right source target) :
    Relates states (fun a _ b _ => a = b) left right source target := by
  refine ⟨?_, related.state, related.events⟩
  rw [related.outcome]
  cases target.outcome <;> rfl

end Execution
end PIR
