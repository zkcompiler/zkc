module

public import ZkcSecurity.ArkLib.FiatShamir.Transcript.Security

@[expose] public section

/-! Actual-execution security for a fixed heterogeneous finite schedule.
The selected claim owns the computation and event. This interface only supplies
a sufficient deterministic failure trace; it does not select security intent.
Terminal knowledge is part of that trace, so a separate terminal failure event
can be handled by a composition theorem without assuming independent games. -/

namespace ZkcSecurity.ArkLib.FiatShamir.Transcript

open Interaction.Oracle Interaction.Oracle.Security
open StateRestoration (Round protocol uniformSchedule)
open OracleComp OracleSpec

universe w

/-- For every total answer table, a claimed failure must yield a terminal
knowledge witness whose backward extraction fails, with all path keys already
present in the actual execution log. Rejected paths need not be completed. -/
def FailureTrace {Input Result : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (admitted : Set Input) (actual : OracleComp (Spec Input rounds) Result)
    (event : Result → Prop) : Prop :=
  ∀ table, event (evalWithAnswerFn (QueryImpl.ofFn table) actual) →
    ∃ (z : Input) (messages : Messages rounds)
      (witness : ((extractor z).terminalState (completedPath rounds z messages table)).Witness),
      z ∈ admitted ∧
      ((extractor z).terminalState (completedPath rounds z messages table)).holds witness ∧
      ¬ (state z).holds ((extractor z).extractWitness (completedPath rounds z messages table) witness) ∧
      ∀ key ∈ completionKeys rounds z messages table,
        key ∈ (tableQueryLog actual table).map Sigma.fst

/-- Reuse the all-prefix knowledge argument on any actual computation with a
proved failure trace. The budget counts that computation's calls, including
repeated keys; there is no additional completion or reduction access. -/
theorem extraction_event_bound {Input Result : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (admitted : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ admitted, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ admitted, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (uniformSchedule error rounds))
    (actual : OracleComp (Spec Input rounds) Result) (event : Result → Prop)
    (trace : FailureTrace state extractor admitted actual event)
    (totalCalls : Nat) (queryBound : IsTotalQueryBound actual totalCalls) :
    Pr{let result ← (simulateQ randomOracle actual).run' ∅}[event result] ≤
      (totalCalls : ENNReal) * error := by
  apply prEvent_randomOracle_le_of_bad_queries actual totalCalls queryBound event
    (badKey state extractor admitted) error
  · exact badKey_resample_bound state extractor admitted error bounded
  · intro table failed
    obtain ⟨z, messages, witness, legal, terminal, initial, covered⟩ := trace table failed
    have failure := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
      (protocol rounds).roles (preserving z legal) _ witness terminal initial
    obtain ⟨key, inPath, bad⟩ := badChallengeOnPath_completion
      (extractor z) z messages table witness failure
    obtain ⟨query, inLog, equal⟩ := List.mem_map.mp (covered key inPath)
    refine ⟨query, inLog, ?_⟩
    change query.1.input ∈ admitted ∧ _
    rw [equal, completionKeys_input rounds z messages table key inPath]
    exact ⟨legal, bad⟩

end ZkcSecurity.ArkLib.FiatShamir.Transcript
