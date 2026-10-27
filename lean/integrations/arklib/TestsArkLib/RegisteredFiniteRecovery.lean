import ZkcArkLib.Knowledge.RegisteredFiniteRecovery
import TestsArkLib.FiniteRecovery

/-! Positive registered evaluation transported to the actual upstream runner,
including arbitrary probabilistic senders and the finite 49-message control. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TestsArkLib.RegisteredFiniteRecovery
open OracleComp OracleSpec
open ZkcSecurity.Commitment.FiniteRecovery
open ZkcSecurity.Claims.FiniteRecovery
open ZkcArkLib.Knowledge.FiniteRecovery
open ZkcArkLib.Knowledge.RegisteredFiniteRecovery

def request : Request Nat := ⟨3⟩
def evaluated : Evaluation registry identifier request 2 := canonical request

example : evaluate registry identifier request 2 = .ok (.ok evaluated) := evaluate_canonical _
theorem registered_native : evaluated.meaning := certify_native evaluated

example (adversary : ProbComp (Nat × Nat)) :
    Pr{let observed ← nativeRun request adversary}[observed.2.2 = true] =
      Pr{let cells ← adversary}[request.Holds (evalWithAnswerFn (answers cells) request.extract)] :=
  acceptance_of_evaluation evaluated registered_native adversary

example (adversary : ProbComp (Nat × Nat)) :
    (fun observed => (observed.1.1, observed.2.2)) <$> nativeRun request adversary =
      run request adversary := observations_eq _ _

example : evalWithAnswerFn (answers (1, 2)) request.extract =
    (extractor request).extractWitness ⟨(1, 2), PUnit.unit⟩ () := registered_extractor evaluated _

/-- Registry evidence cannot change the actual sent oracle or accepted event. -/
example : nativeRun request (pure (1, 2)) = pure ⟨⟨(1, 2), PUnit.unit⟩, (), true⟩ := by
  rw [nativeRun_eq]
  rfl
example : nativeRun request (pure (1, 1)) = pure ⟨⟨(1, 1), PUnit.unit⟩, (), false⟩ := by
  rw [nativeRun_eq]
  rfl

open TestsArkLib.FiniteRecovery in
theorem registered_uniform_recovery :
    Pr{let cells ← ($ᵗ (F7 × F7))}[
      fieldRequest.Holds (evalWithAnswerFn (answers cells) fieldRequest.extract)] = 1 / 7 := by
  have same := acceptance_of_evaluation (canonical fieldRequest)
    (certify_native (canonical fieldRequest)) ($ᵗ (F7 × F7))
  rw [← same]
  exact uniform_acceptance

#print axioms registered_native
#print axioms registered_uniform_recovery
#print axioms ZkcArkLib.Knowledge.RegisteredFiniteRecovery.observations_eq
#print axioms ZkcArkLib.Knowledge.RegisteredFiniteRecovery.acceptance_of_evaluation
#print axioms ZkcArkLib.Knowledge.RegisteredFiniteRecovery.registered_extractor
#print axioms ZkcArkLib.Knowledge.RegisteredFiniteRecovery.certify_native
end TestsArkLib.RegisteredFiniteRecovery
