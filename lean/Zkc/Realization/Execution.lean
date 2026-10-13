module

public import Zkc.Semantics.Execution

@[expose] public section

/-! Execution refinement with coverage of the claimed implementation domain.

The initial relation connects admitted inputs; the final relation constrains
residual state even on stops. Observation transport is available only to
observers respecting that final relation. Probability, adversary resources and
native parsing are separate obligations.
-/

namespace Zkc.Realization
open PIR

variable {S T U E F G O A V : Type}

structure ExecutionSimulation (domain : S → Prop) (specDomain : T → Prop)
    (initial final : S → T → Prop) (left : E → List O) (right : F → List O)
    (implementation : S → Execution S E A) (specification : T → Execution T F A) : Prop where
  covers : ∀ s, domain s → ∃ t, specDomain t ∧ initial s t
  preserves : ∀ s t, domain s → specDomain t → initial s t →
    Related final left right (implementation s) (specification t)

namespace ExecutionSimulation

variable {domain : S → Prop} {specDomain : T → Prop}
  {initial final : S → T → Prop} {left : E → List O} {right : F → List O}
  {implementation : S → Execution S E A} {specification : T → Execution T F A}

/-- A claim cannot evade an admitted implementation input by relating it to
no specification input. An explicitly empty claimed domain remains possible. -/
theorem initial_exists
    (simulation : ExecutionSimulation domain specDomain initial final left right
      implementation specification) (s : S) (admitted : domain s) :
    ∃ t, initial s t := by
  obtain ⟨t, _, related⟩ := simulation.covers s admitted
  exact ⟨t, related⟩

/-- Every predicate of the selected complete observation transports. A
probability bound requires a distribution-preserving correspondence as well. -/
theorem transport
    (simulation : ExecutionSimulation domain specDomain initial final left right
      implementation specification)
    (stateLeft : S → V) (stateRight : T → V)
    (respects : ∀ s t, final s t → stateLeft s = stateRight t)
    (property : Outcome A → V → List O → Prop)
    (proved : ∀ t, specDomain t → property (specification t).outcome
      (stateRight (specification t).state) (observeEvents right (specification t).events)) :
    ∀ s, domain s → property (implementation s).outcome
      (stateLeft (implementation s).state) (observeEvents left (implementation s).events) := by
  intro s admitted
  obtain ⟨t, legal, inputs⟩ := simulation.covers s admitted
  have related := simulation.preserves s t admitted legal inputs
  rw [related.outcome, respects _ _ related.state, related.events]
  exact proved t legal

/-- Adjacent simulations compose through an actually admitted intermediate
input and an actual residual state, rather than independently chosen outputs. -/
theorem compose {targetDomain : U → Prop} {nextInitial nextFinal : T → U → Prop}
    {last : G → List O} {target : U → Execution U G A}
    (first : ExecutionSimulation domain specDomain initial final left right
      implementation specification)
    (second : ExecutionSimulation specDomain targetDomain nextInitial nextFinal right last
      specification target) :
    ExecutionSimulation domain targetDomain
      (fun s u => ∃ t, specDomain t ∧ initial s t ∧ nextInitial t u)
      (fun s u => ∃ t, final s t ∧ nextFinal t u) left last implementation target where
  covers s admitted := by
    obtain ⟨t, legal, st⟩ := first.covers s admitted
    obtain ⟨u, targetLegal, tu⟩ := second.covers t legal
    exact ⟨u, targetLegal, t, legal, st, tu⟩
  preserves s u admitted targetLegal inputs := by
    obtain ⟨t, legal, st, tu⟩ := inputs
    exact related_trans final nextFinal left right last _ _ _
      (first.preserves s t admitted legal st) (second.preserves t u legal targetLegal tu)

/-- Per-operation handler laws establish whole-program simulation for any
well-founded adaptive process. Coverage is still supplied for its entry domain. -/
theorem ofHandlers {I : Signature}
    (h : Handler I S E) (g : Handler I T F) (program : Proc I A)
    (covered : ∀ s, domain s → ∃ t, specDomain t ∧ initial s t)
    (operations : HandlerRelated initial left right h g) :
    ExecutionSimulation domain specDomain initial initial left right
      (program.run h) (program.run g) where
  covers := covered
  preserves s t _ _ inputs := run_related initial left right h g operations program s t inputs

end ExecutionSimulation
end Zkc.Realization
