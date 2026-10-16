module

public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Keys
public import ZkcSecurity.ArkLib.FiatShamir.Transcript.Security

@[expose] public section

/-! Direct bad-query security for actual two-round full-prefix computations.
The claim fixes the computation and event. A deterministic trace law supplies
an accepted terminal witness and the two keys actually queried. No completion
is executed after rejection, and no change of the registered oracle is made.
-/

namespace ZkcSecurity.ArkLib.FiatShamir.Prefix.Direct
open Interaction.Oracle Interaction.Oracle.Security
open StateRestoration (Round protocol uniformSchedule)
open OracleComp OracleSpec

universe w
variable {Input Result : Type} {round : Round}

/-- Reassociate the native prefix coordinates into the generic typed key. -/
def transcriptKey : Prefix.Key Input round → Transcript.Key Input [round, round]
  | .inl (z, m) => .here z m
  | .inr (z, m, c, n) => .later m c (.here z n)

def nativeKey : Transcript.Key Input [round, round] → Prefix.Key Input round
  | .inl (z, m) => .inl (z, m)
  | .inr (m, c, .inl (z, n)) => .inr (z, m, c, n)
  | .inr (_, _, .inr (_, _, impossible)) => nomatch impossible

@[simp] theorem nativeKey_transcriptKey (key : Prefix.Key Input round) :
    nativeKey (transcriptKey key) = key := by cases key <;> rfl

@[simp] theorem transcriptKey_nativeKey (key : Transcript.Key Input [round, round]) :
    transcriptKey (nativeKey key) = key := by
  rcases key with ⟨z, m⟩ | ⟨m, c, key⟩
  · rfl
  · rcases key with ⟨z, n⟩ | ⟨_, _, impossible⟩
    · rfl
    · exact impossible.elim

def keyEquiv : Prefix.Key Input round ≃ Transcript.Key Input [round, round] :=
  ⟨transcriptKey, nativeKey, nativeKey_transcriptKey, transcriptKey_nativeKey⟩

def transcriptTable (table : Prefix.Key Input round → round.Challenge) :
    Transcript.Table Input [round, round]
  | .inl (z, m) => table (.inl (z, m))
  | .inr (m, c, .inl (z, n)) => table (.inr (z, m, c, n))
  | .inr (_, _, .inr (_, _, impossible)) => nomatch impossible

/-- Challenge preservation is heterogeneous because the generic key indexes
its reply type; each native constructor reduces it to this round's challenge. -/
theorem transcriptTable_keyEquiv (table : Prefix.Key Input round → round.Challenge)
    (key : Prefix.Key Input round) : HEq (transcriptTable table (keyEquiv key)) (table key) := by
  cases key <;> rfl

def path (z : Input) (m n : round.Message)
    (table : Prefix.Key Input round → round.Challenge) :
    (protocol [round, round]).tree.ExecutionPath :=
  ⟨m, table (.inl (z, m)), n,
    table (.inr (z, m, table (.inl (z, m)), n)), PUnit.unit⟩

theorem path_eq (z : Input) (m n : round.Message)
    (table : Prefix.Key Input round → round.Challenge) :
    path z m n table = Transcript.completedPath [round, round] z
      (m, n, PUnit.unit) (transcriptTable table) := rfl

def badKey (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol [round, round]).tree (state z))
    (admitted : Set Input) (key : Prefix.Key Input round)
    (table : Prefix.Key Input round → round.Challenge) : Prop :=
  match key with
  | .inl (z, m) => z ∈ admitted ∧
      RoundExtractor.badChallenge (extractor z m).2.2 (table key)
  | .inr (z, m, c, n) => z ∈ admitted ∧
      RoundExtractor.badChallenge (((extractor z m).2.2 c).2.2 n).2.2 (table key)

variable [DecidableEq Input] [DecidableEq round.Challenge]

theorem badKey_resample_bound (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol [round, round]).tree (state z))
    (admitted : Set Input) (error : ENNReal)
    (bounded : ∀ z ∈ admitted, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol [round, round]).roles (uniformSchedule error [round, round]))
    (key : Prefix.Key Input round) (table : Prefix.Key Input round → round.Challenge) :
    Pr{let response ← $ᵗ round.Challenge}[
      badKey state extractor admitted key (Function.update table key response)] ≤ error := by
  rcases key with ⟨z, m⟩ | ⟨z, m, c, n⟩
  all_goals simp only [badKey, Function.update_self]
  all_goals by_cases legal : z ∈ admitted
  · simp only [legal, true_and]
    exact Transcript.keyExtractor_local_bound (extractor z) error (bounded z legal)
      (keyEquiv (.inl (z, m)))
  · simp [legal]
  · simp only [legal, true_and]
    exact Transcript.keyExtractor_local_bound (extractor z) error (bounded z legal)
      (keyEquiv (.inr (z, m, c, n)))
  · simp [legal]

/-- Evidence is required for the claim's event at every table. Terminal
knowledge is part of this event connection, so compositions can charge a
separate terminal failure instead of assuming every accepting opening correct. -/
def FailureTrace (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol [round, round]).tree (state z))
    (admitted : Set Input) (actual : OracleComp (Prefix.Spec Input round) Result)
    (event : Result → Prop) : Prop :=
  ∀ table : Prefix.Key Input round → round.Challenge,
    event (evalWithAnswerFn (QueryImpl.ofFn table) actual) →
    ∃ (z : Input) (m n : round.Message)
      (witness : ((extractor z).terminalState (path z m n table)).Witness),
      z ∈ admitted ∧
      ((extractor z).terminalState (path z m n table)).holds witness ∧
      ¬ (state z).holds ((extractor z).extractWitness (path z m n table) witness) ∧
      .inl (z, m) ∈ (tableQueryLog actual table).map Sigma.fst ∧
      .inr (z, m, table (.inl (z, m)), n) ∈ (tableQueryLog actual table).map Sigma.fst

theorem extraction_event_bound (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol [round, round]).tree (state z))
    (admitted : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ admitted, (extractor z).IsProverPreserving
      (protocol [round, round]).roles)
    (bounded : ∀ z ∈ admitted, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol [round, round]).roles (uniformSchedule error [round, round]))
    (actual : OracleComp (Prefix.Spec Input round) Result) (event : Result → Prop)
    (trace : FailureTrace state extractor admitted actual event)
    (totalCalls : Nat) (queryBound : IsTotalQueryBound actual totalCalls) :
    Pr{let result ← (simulateQ randomOracle actual).run' ∅}[event result] ≤
      (totalCalls : ENNReal) * error := by
  apply prEvent_randomOracle_le_of_bad_queries actual totalCalls queryBound event
    (badKey state extractor admitted) error
  · exact badKey_resample_bound state extractor admitted error bounded
  · intro table failed
    obtain ⟨z, m, n, witness, legal, terminal, initial, first, second⟩ := trace table failed
    have failure := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
      (protocol [round, round]).roles (preserving z legal) _ witness terminal initial
    obtain ⟨key, queried, bad⟩ := Transcript.badChallengeOnPath_completion
      (extractor z) z (m, n, PUnit.unit) (transcriptTable table) _ failure
    simp only [Transcript.completionKeys, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at queried
    rcases queried with rfl | rfl
    · obtain ⟨query, inLog, equal⟩ := List.mem_map.mp first
      refine ⟨query, inLog, ?_⟩
      rw [equal]
      exact ⟨legal, bad⟩
    · obtain ⟨query, inLog, equal⟩ := List.mem_map.mp second
      refine ⟨query, inLog, ?_⟩
      rw [equal]
      exact ⟨legal, bad⟩

end ZkcSecurity.ArkLib.FiatShamir.Prefix.Direct
