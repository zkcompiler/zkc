module

public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Security

@[expose] public section

namespace TestsSecurity.PrefixSimulation
open OracleComp OracleSpec Interaction.Oracle.Security
open ZkcSecurity.ArkLib.FiatShamir.Prefix

/-- Small alphabets make the failure controls kernel-reducible. -/
def round : StateRestoration.Round where
  Message := Bool
  Challenge := Bool
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

instance : DecidableEq round.Challenge := inferInstanceAs (DecidableEq Bool)

def firstKey : Key Bool round := .inl (false, false)
def inconsistentKey : Key Bool round := .inr (false, false, false, false)
def consistentKey : Key Bool round := .inr (false, false, true, false)

/-- Erasing the earlier challenge would collide these two queries. -/
theorem challenge_binding : encode inconsistentKey ≠ encode consistentKey := by decide

/-- The selected statement is part of the oracle key. -/
theorem statement_binding :
    encode firstKey ≠ encode (round := round) (.inl (true, false)) := by decide

/-- The latest message is part of each second-round oracle key. -/
theorem message_binding :
    encode consistentKey ≠ encode (round := round) (.inr (false, false, true, true)) := by decide

/-- An altered earlier salt is outside the injection's image. -/
theorem altered_earlier_salt_rejected :
    decode (round := round) (StateRestoration.Key.later false (some false)
      (StateRestoration.Key.here false false (some true))) = none := rfl

/-- Omitting the current challenge-carrying salt is also outside the image. -/
theorem absent_second_salt_rejected :
    decode (round := round) (StateRestoration.Key.later false none
      (StateRestoration.Key.here false false none)) = none := rfl

/-- This deterministic table separates the genuinely reconstructed first answer
from an adversary's inconsistent claimed first answer. -/
def targetTable : StateRestoration.Table Bool (Salt round) [round, round]
  | .inl _ => true
  | .inr (_, _, .inl (_, _, salt)) => salt.getD false
  | .inr (_, _, .inr (_, _, impossible)) => nomatch impossible

def fullTable : QueryImpl (Spec Bool round) Id
  | .inl _ => true
  | .inr (_, _, challenge, _) => challenge

/-- Query a second-round key before its ancestor, then repeat the same key. -/
def outOfOrder : OracleComp (Spec Bool round) (Bool × Bool × Bool) := do
  let first ← liftM ((Spec Bool round).query inconsistentKey)
  let ancestor ← liftM ((Spec Bool round).query firstKey)
  let repeated ← liftM ((Spec Bool round).query inconsistentKey)
  pure (first, ancestor, repeated)

/-- Inconsistent and out-of-order accesses are answered, not silently rejected or repaired. -/
theorem outOfOrder_answers :
    evalWithAnswerFn fullTable outOfOrder = (false, true, false) := rfl

/-- Translation preserves those answers, including the inconsistent prefix. -/
theorem outOfOrder_translated_answers :
    evalWithAnswerFn (QueryImpl.ofFn targetTable) (simulateQ translate outOfOrder) =
      (false, true, false) := rfl

/-- The full-prefix verifier derives `true`, so its final key carries `true`. -/
theorem full_completion :
    evalWithAnswerFn fullTable (complete (round := round) false false false) =
      (⟨false, true, false, true, PUnit.unit⟩ : Path round) := rfl

/-- Choosing the second salt without the completion access gives a different path. -/
theorem skipped_salt_selection_changes_path :
    StateRestoration.completedPath [round, round] false
      (false, none, false, some false, PUnit.unit) targetTable ≠
        evalWithAnswerFn fullTable (complete (round := round) false false false) := by
  intro h
  exact Bool.false_ne_true (congrArg (fun p : Path round => p.2.2.2.1) h)

/-- The implemented preparation step selects the salt from the actual table answer. -/
theorem prepared_salt :
    evalWithAnswerFn (QueryImpl.ofFn targetTable)
      (prepare (round := round) (false, false, false, ())) =
        (false, (false, none, false, some true, PUnit.unit), ()) := rfl

/-- Prepared completion returns the actual full-prefix path. -/
theorem prepared_completion :
    evalWithAnswerFn (QueryImpl.ofFn targetTable)
      (StateRestoration.restoredExecution [round, round]
        (adversaryMap (pure (false, false, false, ())))) =
      (false, (⟨false, true, false, true, PUnit.unit⟩ : Path round), ()) := rfl

/-- With no adversarial accesses, the reduction still charges its salt-selection query. -/
theorem preparation_not_zero_queries :
    ¬ IsTotalQueryBound (adversaryMap
      (pure (false, false, false, ()) : OracleComp (Spec Bool round) _)) 0 := by
  change ¬ IsTotalQueryBound (prepare (round := round) (false, false, false, ())) 0
  simp only [prepare, isTotalQueryBound_query_bind_iff]
  simp

/-- A deterministic fresh-answer driver makes cache resets observable without
any executable sampling or external randomness in the test. -/
def alternatingDraw : QueryImpl (Spec Bool round) (StateT Bool Id) := fun _ => do
  let answer ← get
  set (!answer)
  pure answer

def repeated : OracleComp (Spec Bool round) (Bool × Bool) := do
  let first ← liftM ((Spec Bool round).query firstKey)
  let second ← liftM ((Spec Bool round).query firstKey)
  pure (first, second)

/-- One shared cache calls the driver once and reuses its answer. -/
theorem shared_cache_reuses_answer :
    ((simulateQ alternatingDraw.withCaching repeated).run' ∅).run false =
      ((false, false), true) := rfl

/-- Omitting caching changes both the answer pair and the final draw state. -/
theorem fresh_answers_disagree :
    (simulateQ alternatingDraw repeated).run false = ((false, true), false) := rfl

/-- Resetting only the cache between two accesses also changes the answer pair. -/
theorem reset_cache_disagrees :
    ((do
      let first ← (alternatingDraw.withCaching firstKey).run' ∅
      let second ← (alternatingDraw.withCaching firstKey).run' ∅
      pure (first, second) : StateT Bool Id (Bool × Bool)).run false) =
        ((false, true), false) := rfl

/-- An inconsistent second query, its ancestor, and a repeat share one cache. -/
theorem cached_outOfOrder_answers :
    ((simulateQ alternatingDraw.withCaching outOfOrder).run' ∅).run false =
      ((false, true, false), false) := rfl

/-- Every full-prefix key is disjoint from a first-round key with a nonempty salt. -/
theorem outside_key_disjoint (key : Key Bool round) :
    encode key ≠ StateRestoration.Key.here false false (some false) := by
  intro h
  have decoded := congrArg decode h
  rw [decode_encode] at decoded
  contradiction

/-- Even a pre-existing outside-image entry cannot influence the full-prefix cache. -/
theorem outside_cache_preserved (cache : (TargetSpec Bool round).QueryCache) :
    view (cache.cacheQuery (StateRestoration.Key.here false false (some false)) true) =
      view cache :=
  view_outside (Input := Bool) (round := round) cache
    (StateRestoration.Key.here false false (some false)) true outside_key_disjoint

end TestsSecurity.PrefixSimulation
