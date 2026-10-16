import ZkcSecurity.ArkLib.FiatShamir.Transcript.Security
import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds
import TestsSecurity.SumcheckFiatShamir

/-! Heterogeneous schedules, nonempty false-acceptance events, and exact budgets.
The controls deliberately query an inconsistent late prefix before the first
round and repeat the query. They exercise the actual cached experiment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.FiniteTranscript

open Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open ZkcSecurity.ArkLib.FiatShamir.Transcript

@[reducible] def testRound (M C : Type) [DecidableEq M] [Finite M] [Finite C] [Nonempty C]
    [SampleableType C] : StateRestoration.Round where
  Message := M
  Challenge := C
  interface := { Query := Unit, toOC := { spec := fun _ => M, impl := fun _ message => message } }
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

@[reducible] def mixed := [testRound Bool (Fin 3), testRound (Fin 5) Bool, testRound Unit (Fin 7)]
def mixedMessages : Messages mixed := (true, 4, (), PUnit.unit)

/-- Actual challenge types vary by round, not just the message payloads. -/
def mixedTable : Table Nat mixed
  | .inl _ => 2
  | .inr (_, _, .inl _) => false
  | .inr (_, _, .inr (_, _, .inl _)) => 6
  | .inr (_, _, .inr (_, _, .inr (_, _, key))) => nomatch key

theorem mixed_completion :
    evalWithAnswerFn (QueryImpl.ofFn mixedTable) (complete mixed 11 mixedMessages) =
      ⟨true, (2 : Fin 3), (4 : Fin 5), false, (), (6 : Fin 7), PUnit.unit⟩ := by
  rw [complete_eval]
  rfl

theorem mixed_budget : IsTotalQueryBound (complete mixed 11 mixedMessages) 3 :=
  complete_queryBound mixed 11 mixedMessages

theorem mixed_underbudget : ¬ IsTotalQueryBound (complete mixed 11 mixedMessages) 2 := by
  intro bounded
  exact Nat.lt_irrefl 0 ((bounded.2 (0 : Fin 3)).2 false).1

theorem typed_prefix_binding :
    (Key.later true (0 : Fin 3) (Key.here 11 (4 : Fin 5)) : Key Nat mixed) ≠
      Key.later true (2 : Fin 3) (Key.here 11 (4 : Fin 5)) := by
  intro equal
  have : (0 : Fin 3) = 2 := congrArg (fun key : Key Nat mixed =>
    match key with | .inl _ => 0 | .inr (_, challenge, _) => challenge) equal
  cases this

theorem round_domains_distinct :
    (Key.here 11 true : Key Nat mixed) ≠ Key.later true (2 : Fin 3) (Key.here 11 (4 : Fin 5)) := by
  intro equal
  cases equal

theorem cached_reply {Input : Type} {rounds : List StateRestoration.Round}
    (key : Key Input rounds) (cache : (Spec Input rounds).QueryCache) (reply : key.Challenge) :
    ((Spec Input rounds).randomOracle key).run (cache.cacheQuery key reply) =
      pure (reply, cache.cacheQuery key reply) :=
  QueryImpl.withCaching_run_some uniformSampleImpl (QueryCache.cacheQuery_self _ _ _)

open TestsSecurity.SumcheckFiatShamir
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir (rounds)

def zeroPolynomial : Zkc.Polynomial.Quadratic F 3 :=
  let zero := Zkc.Protocols.Sumcheck.Common.polynomial zeroCoefficients
  .node zero zero zero

def proofMessages : Messages (rounds (F := F) 3) :=
  (linearMessage, zeroMessage, zeroMessage, PUnit.unit)

def lateKey : Key F (rounds (F := F) 3) :=
  Key.later linearMessage (37 : F) (Key.later zeroMessage (19 : F) (Key.here 1 zeroMessage))

def adaptive : OracleComp (Spec F (rounds (F := F) 3))
    (F × Messages (rounds (F := F) 3) × Unit) := do
  let _ : F ← liftM ((Spec F (rounds (F := F) 3)).query lateKey)
  let reply : F ← liftM ((Spec F (rounds (F := F) 3)).query (Key.here 1 linearMessage))
  let _ : F ← liftM ((Spec F (rounds (F := F) 3)).query lateKey)
  pure (reply, proofMessages, ())

theorem adaptive_budget : IsTotalQueryBound adaptive 3 := by
  exact ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩⟩

theorem repeated_calls_count : ¬ IsTotalQueryBound adaptive 2 := by
  intro bounded
  exact Nat.lt_irrefl 0 ((bounded.2 (0 : F)).2 (0 : F)).1

open ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds

theorem actual_false_acceptance :
    (1 : F) ≠ zeroPolynomial.booleanSum ∧
      accepted 3 zeroPolynomial 1 ⟨linearMessage, (0 : F), zeroMessage, (19 : F),
        zeroMessage, (37 : F), PUnit.unit⟩ := by decide +kernel

theorem wrong_challenge_rejects :
    ¬ accepted 3 zeroPolynomial 1 ⟨linearMessage, (1 : F), zeroMessage, (19 : F),
      zeroMessage, (37 : F), PUnit.unit⟩ := by decide +kernel

theorem adaptive_soundness :
    Pr{let result ← (simulateQ randomOracle (execution (rounds (F := F) 3) adaptive)).run' ∅}[
      accepted 3 zeroPolynomial result.1 result.2.1 ∧ result.1 ≠ zeroPolynomial.booleanSum] ≤
        12 / 101 := by
  have bound := soundness 3 (fun _ : F => zeroPolynomial) id adaptive 3 adaptive_budget
  norm_num [F, ZMod.card, ← mul_div_assoc] at bound ⊢
  exact bound

theorem informative_bound : (12 / 101 : ENNReal) < 1 := by
  exact (ENNReal.div_lt_iff (by simp) (by simp)).mpr (by norm_num)

#print axioms ZkcSecurity.ArkLib.FiatShamir.Transcript.extraction_bound
#print axioms ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds.source_soundness

end TestsSecurity.FiniteTranscript
