module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.EarlyStop
public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Direct

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Direct soundness for the actual early-stopping two-round verifier.
The verifier-level trace law is uniform in the input, messages and answer table.
It is then lifted through an arbitrary adaptive adversary using the same table. -/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FullPrefix

open Interaction.Oracle.Security
open OracleComp OracleSpec
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Protocols.Sumcheck.Common
open ZkcSecurity.ArkLib.FiatShamir

variable {Input F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
variable [DecidableEq Input]

omit [DecidableEq Input] in
/-- Deterministic acceptance under every answer table, including tables reached
after arbitrary prequeries, is exactly the three authored checks. -/
theorem earlyVerify_table_acceptance (statement : Input → Statement F)
    (z : Input) (m n : Message F) (table : Prefix.Key Input (round (F := F)) → F) :
    evalWithAnswerFn (QueryImpl.ofFn table) (earlyVerify statement z m n) = true ↔
      accepted (statement z) m (table (.inl (z, m))) n
        (table (.inr (z, m, table (.inl (z, m)), n))) := by
  by_cases first : wireBoundary m = (statement z).claim
  · by_cases second : wireBoundary n = wireEvaluate m (table (.inl (z, m)))
    · simp [earlyVerify, first, second, accepted, evalWithAnswerFn_bind]
    · simp [earlyVerify, first, second, accepted, evalWithAnswerFn_bind]
  · simp [earlyVerify, first, accepted]

omit [DecidableEq Input] in
/-- Acceptance implies that both full-prefix keys occur in the actual query
log. Rejected runs are neither extended nor equated with completed runs. -/
theorem earlyVerify_acceptance_queries (statement : Input → Statement F)
    (z : Input) (m n : Message F) (table : Prefix.Key Input (round (F := F)) → F)
    (success : evalWithAnswerFn (QueryImpl.ofFn table) (earlyVerify statement z m n) = true) :
    (tableQueryLog (earlyVerify statement z m n) table).map Sigma.fst =
      [.inl (z, m), .inr (z, m, table (.inl (z, m)), n)] := by
  have checks := (earlyVerify_table_acceptance statement z m n table).mp success
  rcases checks with ⟨first, second, final⟩
  simp only [earlyVerify, first, ite_true, tableQueryLog_query_bind, second,
    tableQueryLog_pure, List.map_cons, List.map_nil]

omit [DecidableEq Input] in
/-- The accepted-false-statement event has terminal knowledge and no initial
knowledge, and its challenge keys were queried in the same adversarial run. -/
theorem earlyGame_failureTrace (statement : Input → Statement F)
    (adversary : Adversary Input F) :
    Prefix.Direct.FailureTrace (fun z => inputState (statement z))
      (fun z => statementExtractor (statement z)) Set.univ
      (earlyGame statement adversary)
      (fun result => result.2 = true ∧ (statement result.1).claim ≠
        (polynomial (statement result.1).coefficients).booleanSum) := by
  intro table failed
  rcases selected : evalWithAnswerFn (QueryImpl.ofFn table) adversary with ⟨z, m, n, witness⟩
  simp only [earlyGame, evalWithAnswerFn_bind, selected, evalWithAnswerFn_pure] at failed
  have queries := earlyVerify_acceptance_queries statement z m n table failed.1
  have success := (earlyVerify_table_acceptance statement z m n table).mp failed.1
  refine ⟨z, m, n, terminalWitness (statement z) _ (), Set.mem_univ _, ?_, ?_, ?_, ?_⟩
  · exact (terminal_iff (statement z) m _ n _ ()).mpr success
  · exact fun initial => failed.2 initial.2
  all_goals
    simp only [earlyGame, tableQueryLog_bind, selected, tableQueryLog_pure,
      List.append_nil, List.map_append, queries, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    simp

/-- The direct proof charges only the adversary's accesses and the two accesses
of the real verifier. The initial cache is empty and is shared throughout. -/
theorem early_soundness_direct (statement : Input → Statement F) (adversary : Adversary Input F)
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (earlyGame statement adversary)).run' ∅}[
      result.2 = true ∧ (statement result.1).claim ≠
        (polynomial (statement result.1).coefficients).booleanSum] ≤
          (Q + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    Prefix.Direct.extraction_event_bound
      (fun z => inputState (statement z)) (fun z => statementExtractor (statement z)) Set.univ
      (2 / (Fintype.card F : ENNReal))
      (fun z _ => prover_preserving 2 True (polynomial (statement z).coefficients) (statement z).claim)
      (fun z _ => locally_bounded 2 True (polynomial (statement z).coefficients) (statement z).claim)
      (earlyGame statement adversary) _ (earlyGame_failureTrace statement adversary)
      (Q + 2) (earlyGame_queryBound statement adversary Q queryBound)

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FullPrefix
