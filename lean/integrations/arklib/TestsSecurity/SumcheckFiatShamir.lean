import ZkcSecurity.Examples.SumcheckFiatShamir
import Mathlib.Algebra.Field.ZMod

/-! Kernel-checked failure controls for the canonical restoration consumer. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.SumcheckFiatShamir

open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open OracleComp OracleSpec
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Protocols.Sumcheck.Common
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir

abbrev F := ZMod 101
instance prime : Fact (Nat.Prime 101) := ⟨by decide⟩

def zeroMessage : Message F := ⟨0, 0, 0⟩
def linearMessage : Message F := ⟨0, 1, 0⟩
def zeroCoefficients : Coefficients F := ⟨zeroMessage, zeroMessage, zeroMessage⟩
def falseStatement : Statement F := ⟨zeroCoefficients, 1⟩
def falseMessages := messages linearMessage () zeroMessage ()
def noQueries : Adversary F Unit := pure ⟨falseStatement, falseMessages, ()⟩

theorem noQueries_bound : IsTotalQueryBound noQueries 0 := by trivial

/-- A genuine false claim is accepted for a completed challenge pair; the event
is not made empty by construction or by a supplied security hypothesis. -/
theorem false_acceptance_control :
    falseStatement.claim ≠ (polynomial falseStatement.coefficients).booleanSum ∧
      accepted falseStatement linearMessage 0 zeroMessage 37 := by decide +kernel

/-- In contrast, the unchanged false proof fails after a non-root first challenge. -/
theorem wrong_first_challenge_rejects :
    ¬ accepted falseStatement linearMessage 1 zeroMessage 37 := by decide +kernel

/-- Every earlier failed guard remains failed, even with a zero residual and
messages whose evaluations match on every challenge. -/
theorem failed_prefix_cannot_repair (challenge : F) :
    ¬ RoundExtractor.badChallenge
      (extractor 1 False (rowPolynomial zeroMessage) 0 zeroMessage).2.2 challenge := by
  rw [badChallenge_iff]
  simp

/-- Omitting a boundary guard would allow the zero polynomial to repair a false
claim at every challenge. The actual badChallenge predicate retains that guard. -/
theorem missing_boundary_control (challenge : F) :
    (1 : F) ≠ (rowPolynomial zeroMessage).booleanSum ∧
    zeroMessage.evaluate challenge = ((rowPolynomial zeroMessage).restrict challenge).booleanSum ∧
    ¬ RoundExtractor.badChallenge
      (extractor 1 True (rowPolynomial zeroMessage) 1 zeroMessage).2.2 challenge := by
  rw [badChallenge_iff]
  norm_num [rowPolynomial, zeroMessage, Message.evaluate, Message.boundary,
    Zkc.Polynomial.Quadratic.booleanSum, Zkc.Polynomial.cubeSum,
    Zkc.Polynomial.Quadratic.eval, Zkc.Polynomial.Quadratic.restrict,
    Zkc.Polynomial.Quadratic.add, Zkc.Polynomial.Quadratic.scale]

/-- A final proof with no adversarial query still needs both completion accesses. -/
theorem missing_completion_budget :
    ¬ IsTotalQueryBound (complete (rounds (F := F) 2) falseStatement falseMessages) 1 := by
  intro bound
  change 0 < 1 ∧ ∀ first : F, 0 < 0 ∧ _ at bound
  exact Nat.lt_irrefl 0 (bound.2 0).1

/-- Out-of-order and repeated queries are charged. The final public claim is
chosen from an oracle answer, rather than fixed before the adversary runs. -/
def adaptiveQueries : Adversary F Unit := do
  let value : F ← liftM ((RestorationOracle F Unit).query
    (secondKey falseStatement linearMessage () zeroMessage ()))
  let _ : F ← liftM ((RestorationOracle F Unit).query
    (firstKey falseStatement linearMessage ()))
  let _ : F ← liftM ((RestorationOracle F Unit).query
    (secondKey falseStatement linearMessage () zeroMessage ()))
  pure ⟨⟨zeroCoefficients, value⟩, falseMessages, ()⟩

theorem adaptiveQueries_bound : IsTotalQueryBound adaptiveQueries 3 := by
  exact ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩⟩

theorem repeated_queries_cost : ¬ IsTotalQueryBound adaptiveQueries 2 := by
  intro bound
  exact Nat.lt_irrefl 0 ((bound.2 (0 : F)).2 (0 : F)).1

/-- Re-querying a cached restoration key preserves both its answer and cache.
Fresh independent resampling cannot satisfy this equality. -/
theorem cached_requery (key : RestorationKey F Unit)
    (cache : (RestorationOracle F Unit).QueryCache) (value : key.Challenge) :
    ((RestorationOracle F Unit).randomOracle key).run (cache.cacheQuery key value) =
      pure (value, cache.cacheQuery key value) := by
  exact QueryImpl.withCaching_run_some uniformSampleImpl (QueryCache.cacheQuery_self _ _ _)

/-- Different public statements and latest messages produce different keys. -/
theorem statement_and_message_binding :
    firstKey falseStatement linearMessage () ≠
      firstKey (⟨zeroCoefficients, 0⟩ : Statement F) linearMessage () ∧
    secondKey falseStatement linearMessage () zeroMessage () ≠
      secondKey falseStatement linearMessage () linearMessage () := by decide +kernel

/-- Q=3 gives a strictly informative numerical bound, including two completion accesses. -/
theorem nonvacuous_bound :
    (3 + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal)) < 1 := by
  norm_num [F, ZMod.card, ← mul_div_assoc]
  exact (ENNReal.div_lt_iff (by simp) (by simp)).mpr (by norm_num)

/-- The bound really applies to the cached native game with the adaptive adversary. -/
theorem adaptive_native_soundness :
    Pr{let result ← (simulateQ randomOracle (nativeGame adaptiveQueries)).run' ∅}[
      result.2.2.1 = true ∧ result.1.claim ≠ (polynomial result.1.coefficients).booleanSum] ≤
        10 / 101 := by
  have bound := soundness adaptiveQueries 3 adaptiveQueries_bound
  norm_num [F, ZMod.card, ← mul_div_assoc] at bound ⊢
  exact bound

/-- A fixed-witness bound would not bound ArkLib's existential bad event. -/
theorem existential_witness_control :
    (∀ witness : Fin 7, (Finset.univ.filter fun challenge : Fin 7 =>
      challenge = witness).card ≤ 1) ∧
    (Finset.univ.filter fun challenge : Fin 7 => ∃ witness : Fin 7,
      challenge = witness).card = 7 := by decide +kernel

/-- Early rejection has zero reached PIR challenges, while completion_log still
contains two keys. This prevents promoting acceptance equality to trace equality. -/
theorem first_guard_observation (form : ZkcExamples.NativePrograms.SumcheckVariants.Form) :
    let result := run (ZkcExamples.NativePrograms.SumcheckVariants.verifier form)
      zeroCoefficients 1 0 ⟨zeroMessage, fun _ => zeroMessage⟩ 0 0
    (result.state, result.events.filterMap querySite) = (3, []) := by
  have observations := reached_observations
    (ZkcExamples.NativePrograms.SumcheckVariants.contract (F := F) form)
    falseStatement 0 ⟨zeroMessage, fun _ => zeroMessage⟩ 0 0
  simpa [falseStatement, zeroMessage, wireBoundary] using observations

/-- A failed second boundary preserves the first reached challenge only. -/
theorem second_guard_observation (form : ZkcExamples.NativePrograms.SumcheckVariants.Form) :
    let result := run (ZkcExamples.NativePrograms.SumcheckVariants.verifier form)
      zeroCoefficients 1 0 ⟨linearMessage, fun _ => zeroMessage⟩ 1 0
    (result.state, result.events.filterMap querySite) =
      (8, [ZkcExamples.NativePrograms.Sumcheck.wiring.firstChallenge]) := by
  have observations := reached_observations
    (ZkcExamples.NativePrograms.SumcheckVariants.contract (F := F) form)
    falseStatement 0 ⟨linearMessage, fun _ => zeroMessage⟩ 1 0
  simpa [falseStatement, zeroMessage, linearMessage, wireBoundary, wireEvaluate] using observations

end TestsSecurity.SumcheckFiatShamir
