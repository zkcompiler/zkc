import ZkcArkLib.Knowledge.FiniteRecovery
import Mathlib.Algebra.Field.ZMod

/-! Straight-line recovery controls: exact native access, two-read scope,
wrong relation, missing cell, and a valid but substituted witness. -/
set_option autoImplicit false
namespace TestsArkLib.FiniteRecovery
open OracleComp OracleSpec
open ZkcSecurity.Commitment.FiniteRecovery
open ZkcArkLib.Knowledge.FiniteRecovery

def request : Request Nat := ⟨3⟩

example : evalWithAnswerFn (answers (1, 2)) request.extract = (1, 2) := extract_eq _ _
example : evalWithAnswerFn (answers (1, 2)) request.verifier = true := by decide +kernel
example : IsQueryBoundP request.extract (fun _ => True) 2 := extract_query_bound _
example : ¬ IsQueryBoundP request.extract (fun _ => True) 1 := by
  simp [Request.extract, isQueryBoundP_query_bind_iff]

/-- The substituted constant is a valid sum witness but is not the requested
recovery of the actual input oracle. Relation membership cannot select code. -/
example : request.Holds (3, 0) := rfl
example : evalWithAnswerFn (answers (1, 2)) request.extract ≠ (3, 0) := by simp

/-- Reading the first cell twice changes the access experiment. -/
def firstCellOnly : QueryImpl (Access Nat) Id := fun _ => 1
example : evalWithAnswerFn firstCellOnly request.extract = (1, 1) := rfl
example : ¬ request.Holds (evalWithAnswerFn firstCellOnly request.extract) := by decide +kernel
example : evalWithAnswerFn (answers (1, 2)) (Request.verifier (⟨4⟩ : Request Nat)) = false := by decide +kernel

example : (extractor request).extractWitness ⟨(1, 2), PUnit.unit⟩ () = (1, 2) := rfl
example : request.Holds (evalWithAnswerFn (answers (1, 2)) request.extract) :=
  native_extraction request (1, 2) rfl

example : nativeRun request (pure (1, 2)) = pure ⟨⟨(1, 2), PUnit.unit⟩, (), true⟩ := by
  rw [nativeRun_eq]
  rfl
example : nativeRun request (pure (1, 1)) = pure ⟨⟨(1, 1), PUnit.unit⟩, (), false⟩ := by
  rw [nativeRun_eq]
  rfl

example (adversary : ProbComp (Nat × Nat)) :
    Pr{let observed ← (nativeRun request adversary)}[observed.2.2 = true] =
      Pr{let cells ← adversary}[request.Holds (evalWithAnswerFn (answers cells) request.extract)] :=
  acceptance_eq_recovery _ _

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev F7 := ZMod 7
noncomputable instance : SampleableType F7 := SampleableType.ofFintype F7

def fieldRequest : Request F7 := ⟨3⟩

/-- A completely finite sampled consumer: all 49 two-cell messages are in the
sender's universe, and the seven accepted messages are exactly recoverable. -/
theorem uniform_acceptance :
    Pr{let observed ← (nativeRun fieldRequest ($ᵗ (F7 × F7)))}[observed.2.2 = true] = 1 / 7 := by
  rw [acceptance_eq_recovery]
  simp only [extract_eq]
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun cells : F7 × F7 => fieldRequest.Holds cells).card = 7 := by
    decide +kernel
  rw [count, Fintype.card_prod, ZMod.card]
  change (7 : ENNReal) / 49 = 1 / 7
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

#print axioms uniform_acceptance
#print axioms ZkcArkLib.Knowledge.FiniteRecovery.nativeRun_eq
#print axioms ZkcArkLib.Knowledge.FiniteRecovery.native_extraction
#print axioms ZkcArkLib.Knowledge.FiniteRecovery.acceptance_eq_recovery
end TestsArkLib.FiniteRecovery
