import TestsSecurity.SumcheckFiatShamir
import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native

/-! Controls for the full-prefix and actual early-stop experiment. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.SumcheckFullPrefix

open TestsSecurity.SumcheckFiatShamir
open Interaction.Oracle.Security
open OracleComp OracleSpec
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Protocols.Sumcheck.Common
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir

local instance : DecidableEq (round (F := F)).Challenge := inferInstanceAs (DecidableEq F)

/-- Inconsistent second prefixes and repeated prequeries are valid adversary code. -/
def prequeries : FullPrefix.Adversary (Statement F) F := do
  let _ : F ← liftM ((FullPrefix.Oracle (Statement F) F).query
    (.inr (falseStatement, linearMessage, (37 : F), zeroMessage)))
  let value : F ← liftM ((FullPrefix.Oracle (Statement F) F).query
    (.inl (falseStatement, linearMessage)))
  let _ : F ← liftM ((FullPrefix.Oracle (Statement F) F).query
    (.inr (falseStatement, linearMessage, (37 : F), zeroMessage)))
  pure (⟨zeroCoefficients, value⟩, linearMessage, zeroMessage, ())

theorem prequeries_bound : IsTotalQueryBound prequeries 3 := by
  exact ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩⟩

/-- Query the final statement's first key, an inconsistent second prefix, and
then the actual second key. Both verifier calls will hit the shared cache. -/
def sharedCacheQueries : FullPrefix.Adversary (Statement F) F := do
  let first : F ← liftM ((FullPrefix.Oracle (Statement F) F).query
    (.inl (falseStatement, linearMessage)))
  let _ : F ← liftM ((FullPrefix.Oracle (Statement F) F).query
    (.inr (falseStatement, linearMessage, first + (1 : F), zeroMessage)))
  let _ : F ← liftM ((FullPrefix.Oracle (Statement F) F).query
    (.inr (falseStatement, linearMessage, first, zeroMessage)))
  pure (falseStatement, linearMessage, zeroMessage, ())

theorem sharedCacheQueries_bound : IsTotalQueryBound sharedCacheQueries 3 := by
  exact ⟨by decide, fun _ => ⟨by change 0 < 2; decide,
    fun _ => ⟨by change 0 < 1; decide, fun _ => trivial⟩⟩⟩

theorem shared_cache_direct_soundness :
    Pr{let output ← (simulateQ randomOracle (FullPrefix.earlyGame id sharedCacheQueries)).run' ∅}[
      output.2 = true ∧ output.1.claim ≠ (polynomial output.1.coefficients).booleanSum] ≤
        10 / 101 := by
  have bound := FullPrefix.early_soundness_direct id sharedCacheQueries 3 sharedCacheQueries_bound
  norm_num [F, ZMod.card, ← mul_div_assoc] at bound ⊢
  exact bound

/-- The accepted execution reuses both earlier keys rather than sampling fresh
keys for verification. The inconsistent second prefix stays distinct. -/
theorem shared_cache_query_log :
    (tableQueryLog (FullPrefix.earlyGame id sharedCacheQueries) (fun _ => (0 : F))).map Sigma.fst =
      [.inl (falseStatement, linearMessage),
       .inr (falseStatement, linearMessage, (1 : F), zeroMessage),
       .inr (falseStatement, linearMessage, (0 : F), zeroMessage),
       .inl (falseStatement, linearMessage),
       .inr (falseStatement, linearMessage, (0 : F), zeroMessage)] := by
  decide +kernel

/-- The prior challenge is genuinely part of the second full-prefix key. -/
theorem previous_challenge_binding :
    (Sum.inr (falseStatement, linearMessage, (0 : F), zeroMessage) :
      (FullPrefix.Oracle (Statement F) F).Domain) ≠
      .inr (falseStatement, linearMessage, (37 : F), zeroMessage) := by decide +kernel

/-- Early rejection can issue zero accesses, whereas completion still needs two. -/
theorem early_completion_query_control :
    FullPrefix.earlyVerify id falseStatement zeroMessage zeroMessage = pure false ∧
    IsTotalQueryBound (FullPrefix.earlyVerify id falseStatement zeroMessage zeroMessage) 0 ∧
    ¬ IsTotalQueryBound (FullPrefix.completeVerify id falseStatement zeroMessage zeroMessage) 1 := by
  have rejects : FullPrefix.earlyVerify id falseStatement zeroMessage zeroMessage = pure false := by
    simp [FullPrefix.earlyVerify, falseStatement, zeroMessage, wireBoundary]
  refine ⟨rejects, ?_, ?_⟩
  · rw [rejects]; trivial
  · intro bound
    exact Nat.lt_irrefl 0 (bound.2 (0 : F)).1

/-- The reduction's extra salt-selection access is included in this 12/101 bound. -/
theorem early_adaptive_soundness :
    Pr{let output ← (simulateQ randomOracle (FullPrefix.earlyGame id prequeries)).run' ∅}[
      output.2 = true ∧ output.1.claim ≠ (polynomial output.1.coefficients).booleanSum] ≤
        12 / 101 := by
  have bound := FullPrefix.early_soundness id prequeries 3 prequeries_bound
  norm_num [F, ZMod.card, ← mul_div_assoc] at bound ⊢
  exact bound

theorem informative_full_prefix_bound : (12 / 101 : ENNReal) < 1 := by
  exact (ENNReal.div_lt_iff (by simp) (by simp)).mpr (by norm_num)

/-- The direct proof uses the same adversary, oracle and event, and includes
inconsistent, repeated and out-of-order prequeries in its tighter bound. -/
theorem direct_adaptive_soundness :
    Pr{let output ← (simulateQ randomOracle (FullPrefix.earlyGame id prequeries)).run' ∅}[
      output.2 = true ∧ output.1.claim ≠ (polynomial output.1.coefficients).booleanSum] ≤
        10 / 101 := by
  have bound := FullPrefix.early_soundness_direct id prequeries 3 prequeries_bound
  norm_num [F, ZMod.card, ← mul_div_assoc] at bound ⊢
  exact bound

/-- A false statement can be accepted under a root table: the direct event is
not empty. An honest zero statement is also accepted under every table. -/
theorem direct_acceptance_controls
    (table : (FullPrefix.Oracle (Statement F) F).Domain → F) :
    evalWithAnswerFn (QueryImpl.ofFn (fun _ => (0 : F)))
      (FullPrefix.earlyVerify id falseStatement linearMessage zeroMessage) = true ∧
    evalWithAnswerFn (QueryImpl.ofFn table)
      (FullPrefix.earlyVerify id ⟨zeroCoefficients, 0⟩ zeroMessage zeroMessage) = true := by
  constructor
  · exact (FullPrefix.earlyVerify_table_acceptance _ _ _ _ _).mpr
      false_acceptance_control.2
  · apply (FullPrefix.earlyVerify_table_acceptance _ _ _ _ _).mpr
    simp [accepted, zeroCoefficients, zeroMessage, wireBoundary, wireEvaluate, evaluate]

/-- Changing the first reply to a non-root stops after one call. No second
challenge is inserted by the direct proof, even though completion would query it. -/
theorem rejected_actual_query_log :
    (tableQueryLog (FullPrefix.earlyVerify id falseStatement linearMessage zeroMessage)
      (fun _ => (1 : F))).map Sigma.fst = [.inl (falseStatement, linearMessage)] := by
  decide +kernel

/-- Acceptance reaches two actual calls; initial rejection reaches none. -/
theorem accepting_and_initial_rejection_logs :
    (tableQueryLog (FullPrefix.earlyVerify id falseStatement linearMessage zeroMessage)
      (fun _ => (0 : F))).map Sigma.fst =
      [.inl (falseStatement, linearMessage), .inr (falseStatement, linearMessage, (0 : F), zeroMessage)] ∧
    tableQueryLog (FullPrefix.earlyVerify id falseStatement zeroMessage zeroMessage)
      (fun _ => (0 : F)) = [] := by
  decide +kernel

/-- Acceptance equivalence remains valid after an adversary has cached an
inconsistent second prefix. There is no empty-cache premise on this lemma. -/
theorem prequeried_acceptance (cache : (FullPrefix.Oracle (Statement F) F).QueryCache) :
    Pr{let accepted ← (simulateQ randomOracle
      (FullPrefix.earlyVerify id falseStatement linearMessage zeroMessage)).run' (cache.cacheQuery (.inr (falseStatement, linearMessage, (37 : F), zeroMessage)) (19 : F))}[
        accepted = true] =
    Pr{let accepted ← (simulateQ randomOracle
      (FullPrefix.completeVerify id falseStatement linearMessage zeroMessage)).run' (cache.cacheQuery (.inr (falseStatement, linearMessage, (37 : F), zeroMessage)) (19 : F))}[
        accepted = true] :=
  FullPrefix.earlyVerify_acceptance _ _ _ _ _

/-- The fixed source and construction are actually retained by selection. -/
theorem native_identity_control (choice : Native.Selection Unit F)
    (schedule : Zkc.Protocols.Sumcheck.NativeConstruction.Schedule) :
    Native.binding "source-A" "constructed-A" schedule choice ≠
      Native.binding "source-B" "constructed-A" schedule choice ∧
    Native.binding "source-A" "constructed-A" schedule choice ≠
      Native.binding "source-A" "constructed-B" schedule choice := by
  constructor <;> intro equal
  · have := congrArg Zkc.Protocols.Sumcheck.NativeConstruction.Binding.source equal
    simp [Native.binding] at this
  · have := congrArg Zkc.Protocols.Sumcheck.NativeConstruction.Binding.construction equal
    simp [Native.binding] at this

/-- A same-typed subject that skips all guards is not a valid native consumer. -/
def alwaysAccept (schedule : Zkc.Protocols.Sumcheck.NativeConstruction.Schedule) :
    Native.Subject Unit F := fun choice =>
  .done (.cons true (.cons
    (⟨Native.binding "source" "constructed" schedule choice, [], none⟩ :
      Zkc.Protocols.Sumcheck.NativeConstruction.Transcript Unit F) .nil))

theorem missing_guard_no_denotation
    (schedule : Zkc.Protocols.Sumcheck.NativeConstruction.Schedule) :
    ¬ (∀ choice, alwaysAccept schedule choice =
      Native.reference "source" "constructed" schedule choice) := by
  intro law
  have wrong := law (⟨(), zeroCoefficients, 1, zeroMessage, zeroMessage⟩ : Native.Selection Unit F)
  simp [alwaysAccept, Native.reference, Native.binding,
    Zkc.Protocols.Sumcheck.NativeConstruction.experiment, zeroMessage, wireBoundary] at wrong

end TestsSecurity.SumcheckFullPrefix
