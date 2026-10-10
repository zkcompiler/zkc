import Zkc.Compiler.Analysis.SamplingLocality

/-! Countermodels distinguish provider history, ordinary sampler arguments and
fixed provider replies. These are logical controls, not cryptographic tests. -/
namespace Tests.SamplingAnalysis
open Zkc.Compiler.Analysis
open SamplingLocality

private def bounded : Expression Nat Unit := .sample 0 (.input (.receive 1))
private def env (bound : Nat) : Input Nat → Nat
  | .receive _ => bound
  | .sample _ => 3
  | .entry _ => 0

-- Fixing a provider reply does not eliminate a peer-selected bound.
example : (∀ o, env 2 (.sample o) = env 4 (.sample o)) ∧
    evaluate (fun _ a b => a + b) (fun _ reply bound => reply % bound) (env 2) bounded ≠
    evaluate (fun _ a b => a + b) (fun _ reply bound => reply % bound) (env 4) bounded := by
  constructor
  · intro o; rfl
  · decide

example : ¬ NoDirectReception bounded := by
  intro absent
  exact absent 1 (Or.inr rfl)

example : (provenance bounded).received 1 := by
  exact (received_support bounded 1).mpr (Or.inr rfl)

-- Absorption records a reception as provider history, while an ordinary bound
-- remains direct. Neither classification says that the sample is uniform.
example : (Sampling.sample 2 (Sampling.observe (Sampling.reception 1))
    (Sampling.reception 3)).history 1 ∧
    (Sampling.sample 2 (Sampling.observe (Sampling.reception 1))
    (Sampling.reception 3)).received 3 ∧
    ¬ (Sampling.sample 2 (Sampling.observe (Sampling.reception 1))
    (Sampling.reception 3)).received 1 := by
  exact ⟨Or.inl (Or.inl (Or.inr rfl)), rfl, by simp [Sampling.sample, Sampling.reception]⟩

end Tests.SamplingAnalysis
