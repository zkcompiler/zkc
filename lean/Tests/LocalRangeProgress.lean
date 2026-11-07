module

public import Zkc.Construction.ConnectionLocalRangeProgress

@[expose] public section
set_option autoImplicit false
namespace Tests.LocalRangeProgress
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ConnectionLocalRange

def step (carriers : Carriers) (remaining _index : Nat) :
    PIR.Process (Domain.effects carriers) (Bool × Nat) :=
  if remaining = 0 then .done (false, 0) else .done (true, remaining - 1)

theorem decreases (carriers : Carriers) : StepProgress (step carriers) (fun _ ↦ True) id := by
  intro remaining index _
  by_cases empty : remaining = 0
  · simp [step, empty, PIR.Yields]
  · simp only [step, empty, ↓reduceIte, PIR.Yields, true_and, forall_true_left, id_eq]
    omega

/-- The final check is justified for every schedule, not just index zero. -/
theorem enough_iterations (carriers : Carriers) (remaining : Nat) (indices : List Nat)
    (enough : remaining < indices.length) :
    PIR.Yields (fun result ↦ True ∧ result.1 = false)
      (Finite.fold (gated (step carriers)) indices (true, remaining)) :=
  fold_finished (decreases carriers) indices remaining trivial enough

/-- A budget equal to remaining work can still return the continuing flag.
The final check cannot be erased merely because each step decreases. -/
theorem insufficient_bound (carriers : Carriers) :
    Finite.fold (gated (step carriers)) [7] (true, 1) = .done (true, 0) := by rfl

theorem no_finished_claim (carriers : Carriers) :
    ¬ PIR.Yields (fun result ↦ result.1 = false)
      (Finite.fold (gated (step carriers)) [7] (true, 1)) := by
  rw [insufficient_bound]
  simp [PIR.Yields]

/-- An unchanged continuing state does not satisfy the rank obligation. -/
theorem stagnant_refused (carriers : Carriers) :
    ¬ StepProgress
      (fun value _ ↦ (.done (true, value) : PIR.Process (Domain.effects carriers) (Bool × Nat)))
      (fun _ ↦ True) id := by
  intro progress
  have impossible := (progress 0 0 trivial).2 rfl
  exact Nat.lt_irrefl 0 impossible

/-- Even with a generous budget a source stop remains a stop. Progress of
returned values never proves honest completeness by itself. -/
theorem stop_preserved (carriers : Carriers) :
    Finite.fold (gated (fun (_value _index : Nat) ↦
      (PIR.Process.halt .exhausted : PIR.Process (Domain.effects carriers) (Bool × Nat))))
      [3, 5, 7] (true, 11) = .halt .exhausted := by rfl

#print axioms enough_iterations
#print axioms no_finished_claim
#print axioms stagnant_refused
end Tests.LocalRangeProgress
