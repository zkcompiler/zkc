module

public import ZkcExamples.NativePrograms.SchnorrVariants
public import ZkcSecurity.VCVio.Schnorr.FiatShamir
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Actual imported source forms consume one FS connection. Finite controls use
ZMod 5 as both scalar and additive group, with no discrete-log hardness claim.
-/
namespace ZkcSecurity.Examples.SchnorrFiatShamir
open OracleComp OracleSpec
open Zkc.Protocols.Schnorr Zkc.Protocols.Schnorr.Construction
open ZkcSecurity.VCVio.Schnorr.FiatShamir
open ZkcExamples.NativePrograms

section Sources
variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G] [DecidableEq F] [SampleableType F] [DecidableEq Context]
  [Fintype F] [Inhabited F]

/-- This quantifies over all three retained source certificates, not one source hash. -/
theorem source_extraction (form : SchnorrVariants.Form) (service : Nat)
    (prover : Prover Context F G) (binding : Binding Context G) (budget : Nat)
    (queryBound : _root_.FiatShamir.nmaHashQueryBound (Binding Context G)
      (prover binding.key binding) budget) :
    let acc := acceptance (construct (SchnorrVariants.verifier form) service) prover binding
    acc * (acc / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← extractor prover binding budget}[witness • binding.base = binding.key] :=
  extraction (SchnorrVariants.contract form) (construct_realizes _ _) prover binding budget queryBound
end Sources

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5

def binding : Binding String Scalar :=
  ⟨"retained-schnorr-source", "typed-cached-ro/0", "example", 1, 2⟩

def actual : Construction.Verifier String Scalar Scalar :=
  construct (SchnorrVariants.verifier .helpers) 0

def honest : Prover String Scalar Scalar := fun _ message => do
  let challenge ← HasQuery.query (spec := Binding String Scalar × Scalar →ₒ Scalar) (message, 3)
  pure (3, 3 + challenge * 2)

/-- A zero-query prover still obliges the verifier to query the oracle. -/
def noQuery : Prover String Scalar Scalar := fun _ _ => pure (3, 3)

def answers (challenge : Scalar) : QueryImpl (_root_.FiatShamir.Fork.wrappedSpec Scalar) Id :=
  QueryImpl.ofFn (fun n : Nat => (0 : Fin (n + 1))) +
    QueryImpl.ofFn (fun _ : Unit => challenge)

theorem honest_bound : _root_.FiatShamir.nmaHashQueryBound (Binding String Scalar)
    (honest binding.key binding) 1 := by
  change IsQueryBoundP
    ((liftM ((Oracle String Scalar Scalar).query (.inr (binding, 3))) :
      OracleComp (Oracle String Scalar Scalar) Scalar) >>= fun challenge =>
      pure (3, 3 + challenge * 2)) _ 1
  simp

theorem noQuery_bound : _root_.FiatShamir.nmaHashQueryBound (Binding String Scalar)
    (noQuery binding.key binding) 0 := by trivial

def trace (prover : Prover String Scalar Scalar) :=
  _root_.FiatShamir.Fork.runTrace (sigma binding.base) (generable binding.base)
    (Binding String Scalar)
    (_root_.FiatShamir.proverWithFinalQuery (sigma binding.base) (generable binding.base)
      (Binding String Scalar) prover binding) binding.key

/-- Final verification reuses a hit; it does not request a second fresh challenge. -/
theorem honest_cached_log : evalWithAnswerFn (answers 4)
    ((fun result => result.queryLog.length) <$> trace honest) = 1 := by decide +kernel

theorem final_query_is_charged : evalWithAnswerFn (answers 0)
    ((fun result => result.queryLog.length) <$> trace noQuery) = 1 := by decide +kernel

theorem final_query_can_reject : evalWithAnswerFn (answers 1)
    (verificationRun actual noQuery binding) = false := by decide +kernel

theorem honest_accepts : evalWithAnswerFn (answers 4)
    (verificationRun actual honest binding) = true := by decide +kernel

/-- Erasing the key component of the statement merges distinct supported subjects. -/
theorem omitted_statement_collision :
    binding ≠ { binding with key := 4 } ∧
    (binding.context, (3 : Scalar)) = (({ binding with key := 4 } : Binding String Scalar).context, 3) := by
  decide +kernel

theorem statement_bound : (binding, (3 : Scalar)) ≠
    ({ binding with key := 4 }, (3 : Scalar)) := by decide +kernel

theorem context_bound : (binding, (3 : Scalar)) ≠
    ({ binding with context := "different-application" }, (3 : Scalar)) := by decide +kernel

theorem source_bound : (binding, (3 : Scalar)) ≠
    ({ binding with source := "different-source" }, (3 : Scalar)) := by decide +kernel

theorem construction_bound : (binding, (3 : Scalar)) ≠
    ({ binding with construction := "different-construction" }, (3 : Scalar)) := by decide +kernel

theorem base_bound : (binding, (3 : Scalar)) ≠
    ({ binding with base := 4 }, (3 : Scalar)) := by decide +kernel

theorem commitment_bound : (binding, (3 : Scalar)) ≠ (binding, (4 : Scalar)) := by decide +kernel

/-- A false response rejects under an explicitly fixed challenge. -/
theorem wrong_response_rejected : evalWithAnswerFn
    (QueryImpl.ofFn (fun n : Nat => (0 : Fin (n + 1))) +
      QueryImpl.ofFn (fun _ : Binding String Scalar × Scalar => (1 : Scalar)))
    (verify actual binding (3, 1)) = false := by decide +kernel

/-- A fresh query supplies the challenge; final verification reuses that answer. -/
theorem honest_run : verificationRun actual honest binding = (do
    let _ ← _root_.FiatShamir.Fork.wrappedChallengeQuery Scalar
    pure true) := by
  unfold verificationRun
  simp_rw [show actual = construct (SchnorrVariants.verifier .helpers) 0 from rfl,
    verify_eq (SchnorrVariants.contract .helpers) (construct_realizes _ _)]
  simp [honest, _root_.FiatShamir, sigma, HasQuery.query,
    QueryImpl.simulateQ_add_liftM_query_right, _root_.FiatShamir.Fork.roImpl,
    StateT.run'_eq, monad_norm, binding]

theorem honest_acceptance : acceptance actual honest binding = 1 := by
  unfold acceptance
  rw [honest_run]
  simp

/-- A strictly positive lower bound for a nonzero key in the finite model. -/
theorem positive_extraction : (2⁻¹ - 5⁻¹ : ENNReal) ≤
    Pr{let witness ← extractor honest binding 1}[witness • binding.base = binding.key] := by
  have bound := extraction (SchnorrVariants.contract .helpers)
    (construct_realizes (SchnorrVariants.verifier .helpers) 0) honest binding 1 honest_bound
  dsimp only at bound
  rw [show acceptance (construct (SchnorrVariants.verifier .helpers) 0) honest binding = 1
    from honest_acceptance] at bound
  simpa only [_root_.FiatShamir.challengeSpaceInv, Scalar, ZMod.card,
    Nat.cast_ofNat, one_mul, one_div, Nat.cast_one, one_add_one_eq_two] using bound

theorem extraction_bound_positive : (0 : ENNReal) < 2⁻¹ - 5⁻¹ := by
  apply tsub_pos_iff_lt.mpr
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

/-- Different answers to successive fresh requests expose an illicit reset. -/
def successiveAnswers : QueryImpl (_root_.FiatShamir.Fork.wrappedSpec Scalar) (StateM Nat) :=
  ((fun n : Nat => pure (0 : Fin (n + 1))) : QueryImpl unifSpec (StateM Nat)) +
    ((fun _ : Unit => do
      let count ← get
      set (count + 1)
      pure (if count = 0 then (0 : Scalar) else 1)) : QueryImpl (Unit →ₒ Scalar) (StateM Nat))

def resetVerificationRun : OracleComp (_root_.FiatShamir.Fork.wrappedSpec Scalar) Bool := do
  let impl := _root_.FiatShamir.Fork.unifForward (Binding String Scalar) Scalar Scalar +
    _root_.FiatShamir.Fork.roImpl (Binding String Scalar) Scalar Scalar
  let proof ← (simulateQ impl (honest binding.key binding)).run' (∅, [])
  (simulateQ impl (verify actual binding proof)).run' (∅, [])

theorem shared_cache_accepts :
    (simulateQ successiveAnswers (verificationRun actual honest binding)).run 0 = (true, 1) := by
  rfl

theorem reset_cache_rejects :
    (simulateQ successiveAnswers resetVerificationRun).run 0 = (false, 2) := by
  rfl

/-- Without final verification a zero-query output has no fork point at all. -/
theorem missing_final_query_not_forkable :
    evalWithAnswerFn (answers 0)
      ((fun result => (_root_.FiatShamir.Fork.forkPoint Scalar Scalar Scalar
        (Binding String Scalar) 0 result).isSome) <$>
        _root_.FiatShamir.Fork.runTrace (sigma binding.base) (generable binding.base)
          (Binding String Scalar)
          { main := fun _ => pure ((binding, (3, 3)), ∅) } binding.key) = false := by
  decide +kernel

end ZkcSecurity.Examples.SchnorrFiatShamir
