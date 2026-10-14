import ZkcSecurity.ArkLib.FiatShamir.Transcript.Direct
import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds

/-! A reusable finite-schedule consumer with an actual rejecting branch.
This is a regression use of the generic interface, not a native-loop claim.
The actual native zero/one/two-query instance is checked in SumcheckFullPrefix. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.ActualTranscript

open Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open Zkc.Polynomial
open ZkcSecurity.ArkLib.FiatShamir
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds

variable {Input F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

def guardedGame (n : Nat) (admission : Input → Bool)
    (adversary : OracleComp (Transcript.Spec Input (rounds (F := F) n))
      (Input × Transcript.Messages (rounds (F := F) n) × Unit)) :
    OracleComp (Transcript.Spec Input (rounds (F := F) n)) (Option (Input × Path (F := F) n)) := do
  let (z, messages, _) ← adversary
  if admission z then
    let path ← Transcript.complete (rounds (F := F) n) z messages
    pure (some (z, path))
  else pure none

def failureEvent (n : Nat) (polynomial : Input → Quadratic F n) (claim : Input → F) :
    Option (Input × Path (F := F) n) → Prop
  | none => False
  | some (z, path) => accepted n (polynomial z) (claim z) path ∧ claim z ≠ (polynomial z).booleanSum

theorem guarded_trace (n : Nat) (polynomial : Input → Quadratic F n) (claim : Input → F)
    (admission : Input → Bool) (adversary : OracleComp (Transcript.Spec Input (rounds (F := F) n))
      (Input × Transcript.Messages (rounds (F := F) n) × Unit)) :
    Transcript.FailureTrace (fun z => residualState True (polynomial z) (claim z))
      (fun z => extractor n True (polynomial z) (claim z)) Set.univ
      (guardedGame n admission adversary) (failureEvent n polynomial claim) := by
  intro table failed
  rcases selected : evalWithAnswerFn (QueryImpl.ofFn table) adversary with ⟨z, messages, token⟩
  cases eligible : admission z
  · simp [guardedGame, evalWithAnswerFn_bind, selected, eligible, failureEvent] at failed
  · simp only [guardedGame, evalWithAnswerFn_bind, selected, eligible, ite_true,
      Transcript.complete_eval, evalWithAnswerFn_pure, failureEvent] at failed
    refine ⟨z, messages, witness n True (polynomial z) (claim z) _, Set.mem_univ _, ?_, ?_, ?_⟩
    · exact (witness_iff n True (polynomial z) (claim z) _).mpr ⟨trivial, failed.1⟩
    · exact fun initial => failed.2 initial.2
    · intro key inPath
      simp only [guardedGame, tableQueryLog_bind, selected, eligible,
        ite_true, tableQueryLog_pure, List.append_nil, List.map_append,
        Transcript.complete_log_keys, List.mem_append]
      exact Or.inr inPath

theorem guarded_bound (n : Nat) (admission : Input → Bool)
    (adversary : OracleComp (Transcript.Spec Input (rounds (F := F) n))
      (Input × Transcript.Messages (rounds (F := F) n) × Unit))
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (guardedGame n admission adversary) (Q + n) := by
  apply isTotalQueryBound_bind queryBound
  rintro ⟨z, messages, _⟩
  cases eligible : admission z
  · simp only [eligible, Bool.false_eq_true, ite_false]
    trivial
  · simp only [eligible, ite_true, ← map_eq_pure_bind,
      IsTotalQueryBound, isQueryBound_map_iff]
    simpa only [IsTotalQueryBound, rounds_length] using
      Transcript.complete_queryBound (rounds (F := F) n) z messages

/-- The same generic actual-trace theorem applies to all configured counts,
including zero; zero rounds still checks the final constant relation. -/
theorem guarded_soundness (n : Nat) (polynomial : Input → Quadratic F n) (claim : Input → F)
    (admission : Input → Bool) (adversary : OracleComp (Transcript.Spec Input (rounds (F := F) n))
      (Input × Transcript.Messages (rounds (F := F) n) × Unit))
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let output ← (simulateQ randomOracle (guardedGame n admission adversary)).run' ∅}[
      failureEvent n polynomial claim output] ≤
      ((Q + n : Nat) : ENNReal) * (2 / (Fintype.card F : ENNReal)) :=
  Transcript.extraction_event_bound _ _ Set.univ (2 / (Fintype.card F : ENNReal))
    (fun z _ => prover_preserving n True (polynomial z) (claim z))
    (fun z _ => locally_bounded n True (polynomial z) (claim z))
    (guardedGame n admission adversary) _ (guarded_trace n polynomial claim admission adversary)
    (Q + n) (guarded_bound n admission adversary Q queryBound)

/-- Admission failure performs no completion accesses for any answer table. -/
theorem rejected_log (n : Nat) (z : Input) (messages : Transcript.Messages (rounds (F := F) n))
    (table : Transcript.Table Input (rounds (F := F) n)) :
    tableQueryLog (guardedGame n (fun _ => false) (pure (z, messages, ()))) table = [] := by
  simp [guardedGame]

#print axioms ZkcSecurity.ArkLib.FiatShamir.Transcript.extraction_event_bound
#print axioms guarded_soundness

end TestsSecurity.ActualTranscript
