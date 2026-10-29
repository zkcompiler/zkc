import ZkcSecurity.Obligations.RepeatedComponent
import Tests.Obligations

set_option autoImplicit false
noncomputable section
namespace TestsSecurity.PropertyCost
open Zkc.Obligations Zkc.Transcript ZkcSecurity.FiatShamir
open ZkcSecurity.Obligations.RepeatedComponent
open Tests.Obligations

def counter : ComponentInterface bitSignature Unit (Nat × Nat) (Nat × Nat) where
  Parameters := Unit
  Input := Unit
  InputWitness := Unit
  Output := Unit
  OutputWitness := Unit
  input := ClaimRelation.exact (fun _ _ => True)
  output := ClaimRelation.exact (fun _ _ => True)
  Scope _ _ _ := True
  inputView _ _ _ := some ()
  outputView _ _ _ _ := some ()
  body runtime := .call () fun _ => .done (runtime.1 + 1, runtime.2)

def price (history : List Unit) (_ : Unit) : ENNReal := (history.length + 1 : Nat)

/-- Exact accumulated cost, with no global bound on the starting history. -/
def budget : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, depth => depth + 1 + budget count (depth + 1)

theorem frame (privateValue : Nat) :
    Zkc.Obligations.RepeatedComponent.FrameContract counter (fun _ runtime => runtime.2 = privateValue) :=
  fun _ _ holds _ => holds

theorem allocation (privateValue : Nat) :
    CostContract counter queryBit price (fun _ runtime => runtime.2 = privateValue)
      (fun count history _ => budget count history.length) := by
  intro remaining history runtime _
  change ∃ available, price history () + available ≤ (budget (remaining + 1) history.length : ENNReal) ∧
    ∀ _ : Bool, (budget remaining (history ++ [()]).length : ENNReal) ≤ available
  refine ⟨(budget remaining (history.length + 1) : ENNReal), ?_, ?_⟩
  · simp [price, budget]
  · intro _
    simp

theorem symbolic_cost (count : Nat) (history : List Unit) (runtime : Nat × Nat) :
    Typed.ChargedCostBound queryBit price (PIR.repeatN count counter.body runtime)
      history (budget count history.length) :=
  cost_repeatN counter (fun _ value => value.2 = runtime.2)
    (fun count history _ => budget count history.length) (frame runtime.2) (allocation runtime.2)
    count history runtime rfl

example : price [] () = 1 ∧ price [()] () = 2 := by simp [price]

/-- Two calls cost at least three, because the second query sees the first.
Pricing both calls as if they began at the empty history is refused. -/
theorem history_reset_refused :
    ¬ Typed.ChargedCostBound queryBit price (PIR.repeatN 2 counter.body (0, 9)) [] 2 := by
  intro bounded
  simp only [PIR.repeatN, counter, PIR.Process.bind, Typed.ChargedCostBound,
    queryBit, price, List.length_nil, List.length_append, List.length_cons,
    Nat.cast_add, Nat.cast_one, zero_add] at bounded
  norm_num only at bounded
  obtain ⟨remaining, first, rest⟩ := bounded
  obtain ⟨tail, second, _⟩ := rest false
  have atLeastTwo : (2 : ENNReal) ≤ remaining :=
    (le_add_of_nonneg_right (bot_le : (0 : ENNReal) ≤ tail)).trans second
  have impossible : (3 : ENNReal) ≤ 2 := calc
    3 = 1 + (2 : ENNReal) := by norm_num
    _ ≤ 1 + remaining := add_le_add (le_refl 1) atLeastTwo
    _ ≤ 2 := first
  norm_num at impossible

/-- A state-dependent query allowance: once used, further iterations are free.
The rule must reserve the suffix cost for the actual returned state. -/
def once : ComponentInterface bitSignature Unit Bool Bool where
  Parameters := Unit
  Input := Unit
  InputWitness := Unit
  Output := Unit
  OutputWitness := Unit
  input := ClaimRelation.exact (fun _ _ => True)
  output := ClaimRelation.exact (fun _ _ => True)
  Scope _ _ _ := True
  inputView _ _ _ := some ()
  outputView _ _ _ _ := some ()
  body pending := if pending then .call () fun _ => .done false else .done false

def onceBudget (count : Nat) (history : List Unit) (pending : Bool) : ENNReal :=
  if count = 0 then 0 else if pending then price history () else 0

theorem onceFrame : Zkc.Obligations.RepeatedComponent.FrameContract once (fun _ _ => True) := by
  intro _ pending _
  cases pending <;> simp [once, PIR.Yields]

theorem onceAllocation : CostContract once queryBit price (fun _ _ => True) onceBudget := by
  intro remaining history pending _
  cases pending
  · change onceBudget remaining history false ≤ onceBudget (remaining + 1) history false
    simp [onceBudget]
  · change ∃ available, price history () + available ≤ onceBudget (remaining + 1) history true ∧
      ∀ _ : Bool, onceBudget remaining (history ++ [()]) false ≤ available
    refine ⟨0, ?_, ?_⟩ <;> simp [onceBudget]

theorem once_cost (count : Nat) (history : List Unit) (pending : Bool) :
    Typed.ChargedCostBound queryBit price (PIR.repeatN count once.body pending)
      history (onceBudget count history pending) :=
  cost_repeatN once (fun _ _ => True) onceBudget onceFrame onceAllocation count history pending trivial

#print axioms cost_repeatN
#print axioms symbolic_cost
#print axioms history_reset_refused
#print axioms once_cost
end TestsSecurity.PropertyCost
