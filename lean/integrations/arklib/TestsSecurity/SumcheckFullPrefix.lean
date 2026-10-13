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

end TestsSecurity.SumcheckFullPrefix
