import Zkc.Modules.FactorState

/-! Plan search consumes the factor domain and its independent admission check. -/

set_option autoImplicit false
namespace Zkc.Compiler.FactorReuse
open Zkc.Modules.Factor
variable {K : Type}

def infer (facts : List Fact) (available : List Nat) (q : Query) : Plan :=
  match facts.find? (eligible available q) with
  | none => .direct
  | some f => .reuse f (q.point.drop f.applied.length)

theorem inferred_checked (facts : List Fact) (available : List Nat) (q : Query) :
    check facts available q (infer facts available q) = true := by
  unfold infer
  split
  · rfl
  · rename_i f hf
    obtain ⟨hm,he⟩ := List.mem_of_find?_eq_some hf, List.find?_some hf
    exact decide_eq_true ⟨hm,he,rfl⟩

theorem inferred_value (s : State K) (facts : List Fact) (available : List Nat)
    (q : Query) (valid : Valid s facts) :
    runPlan s q (infer facts available q) = runQuery s q :=
  checked_value s facts available q _ valid (inferred_checked facts available q)

open Zkc.Modules.FactorState in
theorem inferred_ready (facts : List Fact) (available : List Nat) (q : Query)
    (ready : Ready available q) : checkPlan facts available q (infer facts available q) = true := by
  simp [checkPlan,checkReady,ready,inferred_checked]

end Zkc.Compiler.FactorReuse
