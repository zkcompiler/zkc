/-
Query-log extraction argument adapted from ArkLib StateRestoration.lean.
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in ArkLib's LICENSE file.
Original author: Quang Dao.
-/
module

public import ZkcSecurity.ArkLib.FiatShamir.Transcript.Experiment

@[expose] public section

/-! Direct full-prefix Fiat–Shamir extraction from all-prefix knowledge laws.

The proof uses ArkLib's backward-extraction failure lemma and VCVio's adaptive
bad-query bound. It introduces no salt-selection accesses or assumed simulation.
The oracle is classical, typed and shared from an empty initial cache. Efficient
extraction, cryptographic hardness and concrete hash realization are separate.
-/

namespace ZkcSecurity.ArkLib.FiatShamir.Transcript
open Interaction.Oracle Interaction.Oracle.Security
open StateRestoration (Round protocol uniformSchedule)
open OracleComp OracleSpec

universe w

theorem badChallengeOnPath_completion {Input : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (z : Input) (messages : Messages rounds) (table : Table Input rounds)
    (witness : (extractor.terminalState (completedPath rounds z messages table)).Witness)
    (bad : extractor.BadChallengeOnPath (protocol rounds).roles
      (completedPath rounds z messages table) witness) :
    ∃ key ∈ completionKeys rounds z messages table,
      RoundExtractor.badChallenge (keyExtractor extractor key).2 (table key) := by
  induction rounds generalizing state with
  | nil => exact bad.elim
  | cons round rounds ih =>
    rcases messages with ⟨message, messages⟩
    rcases bad with bad | bad
    · exact ⟨Key.here z message, List.mem_cons_self, _, bad.2.1, bad.2.2⟩
    · obtain ⟨key, queried, failing⟩ := ih
        ((extractor message).2.2 (table (Key.here z message))).2.2 messages
        (fun key => table (Key.later message (table (Key.here z message)) key)) witness bad
      exact ⟨Key.later message (table (Key.here z message)) key,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key, queried, rfl⟩), failing⟩

def badKey {Input : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (admitted : Set Input) (key : Key Input rounds) (table : Table Input rounds) : Prop :=
  key.input ∈ admitted ∧
    RoundExtractor.badChallenge (keyExtractor (extractor key.input) key).2 (table key)

/-- The tested reply is fresh relative to an entirely arbitrary background
table. Earlier challenges live in the key, independently of that table. -/
theorem badKey_resample_bound {Input : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (admitted : Set Input) (error : ENNReal)
    (bounded : ∀ z ∈ admitted, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (uniformSchedule error rounds))
    (key : Key Input rounds) (table : Table Input rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      badKey state extractor admitted key (Function.update table key response)] ≤ error := by
  simp only [badKey, Function.update_self]
  by_cases legal : key.input ∈ admitted
  · simp only [legal, true_and]
    exact keyExtractor_local_bound (extractor key.input) error (bounded key.input legal) key
  · simp [legal]

theorem extraction_failure_queried {Input W : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (admitted : Set Input)
    (preserving : ∀ z ∈ admitted, (extractor z).IsProverPreserving (protocol rounds).roles)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (Spec Input rounds) (Input × Messages rounds × W))
    (table : Table Input rounds)
    (bad : let result := evalWithAnswerFn (QueryImpl.ofFn table) (execution rounds adversary)
      result.1 ∈ admitted ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))) :
    ∃ query ∈ tableQueryLog (execution rounds adversary) table,
      badKey state extractor admitted query.1 table := by
  let result := evalWithAnswerFn (QueryImpl.ofFn table) adversary
  rcases actual : result with ⟨z, messages, witness⟩
  have evaluated : evalWithAnswerFn (QueryImpl.ofFn table) (execution rounds adversary) =
      (z, completedPath rounds z messages table, witness) := by
    simp only [execution, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (result.1,
      evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds result.1 result.2.1), result.2.2) = _
    rw [actual, complete_eval]
  dsimp only at bad
  rw [evaluated] at bad
  have failing := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
    (protocol rounds).roles (preserving z bad.1) _ _ bad.2.1 bad.2.2
  obtain ⟨key, queried, localFailure⟩ := badChallengeOnPath_completion
    (extractor z) z messages table _ failing
  have input := completionKeys_input rounds z messages table key queried
  have inLog : key ∈ (tableQueryLog (complete rounds z messages) table).map Sigma.fst := by
    rwa [complete_log_keys]
  obtain ⟨query, inLog, equal⟩ := List.mem_map.mp inLog
  refine ⟨query, ?_, ?_⟩
  · simp only [execution, tableQueryLog_bind]
    apply List.mem_append_right
    change query ∈ tableQueryLog (complete rounds result.1 result.2.1) table ++ _
    rw [actual]
    exact List.mem_append_left _ inLog
  · change query.1.input ∈ admitted ∧ _
    rw [equal, input]
    exact ⟨bad.1, localFailure⟩

/-- For `k` heterogeneous rounds, the same classical oracle serves the adaptive
adversary's `Q` calls and exactly `k` completion accesses. Every local security
premise is explicit; the theorem makes no arbitrary-protocol security claim. -/
theorem extraction_bound {Input W : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (admitted : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ admitted, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ admitted, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (uniformSchedule error rounds))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (Spec Input rounds) (Input × Messages rounds × W))
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (execution rounds adversary)).run' ∅}[
      result.1 ∈ admitted ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))] ≤
      ((Q + rounds.length : Nat) : ENNReal) * error := by
  apply prEvent_randomOracle_le_of_bad_queries _ (Q + rounds.length)
    (execution_queryBound rounds adversary Q queryBound) _ (badKey state extractor admitted) error
  · exact badKey_resample_bound state extractor admitted error bounded
  · exact extraction_failure_queried state extractor admitted preserving terminalWitness adversary

end ZkcSecurity.ArkLib.FiatShamir.Transcript
