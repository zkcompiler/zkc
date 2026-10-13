/-
Completion and query-log proofs adapted from ArkLib StateRestoration.lean.
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in ArkLib's LICENSE file.
Original author: Quang Dao.
-/
module

public import ZkcSecurity.ArkLib.FiatShamir.Transcript.Keys

@[expose] public section

/-! Cached full-prefix completion for any fixed finite heterogeneous schedule.
The actual challenge reply is retained in every subsequent query key. Adversary
queries and verifier completion use the same cache; all entered accesses count.
-/

namespace ZkcSecurity.ArkLib.FiatShamir.Transcript
open Interaction.Oracle Interaction.Oracle.Security
open StateRestoration (Round protocol)
open OracleComp OracleSpec

def Messages : List Round → Type
  | [] => PUnit
  | round :: rounds => round.Message × Messages rounds

def prependQuery {Input : Type} {round : Round} {rounds : List Round}
    (message : round.Message) (challenge : round.Challenge) :
    QueryImpl (Spec Input rounds) (OracleComp (Spec Input (round :: rounds))) :=
  fun key => liftM ((Spec Input (round :: rounds)).query (Key.later message challenge key))

def complete {Input : Type} : (rounds : List Round) → Input → Messages rounds →
    OracleComp (Spec Input rounds) (protocol rounds).tree.ExecutionPath
  | [], _, _ => pure PUnit.unit
  | round :: rounds, z, (message, messages) => do
    let challenge ← liftM ((Spec Input (round :: rounds)).query (Key.here z message))
    let path ← simulateQ (prependQuery message challenge) (complete rounds z messages)
    pure ⟨message, ⟨challenge, path⟩⟩

theorem complete_queryBound {Input : Type} (rounds : List Round) (z : Input)
    (messages : Messages rounds) : IsTotalQueryBound (complete rounds z messages) rounds.length := by
  induction rounds with
  | nil => trivial
  | cons round rounds ih =>
    rcases messages with ⟨message, messages⟩
    simp only [complete, List.length_cons, isTotalQueryBound_query_bind_iff, Nat.add_sub_cancel]
    refine ⟨by omega, fun challenge => ?_⟩
    have h := (ih messages).simulateQ_of_step_le (step := 1)
      (fun key => show IsTotalQueryBound
        (prependQuery (Input := Input) message challenge key) 1 from by
          change IsTotalQueryBound
            (liftM ((Spec Input (round :: rounds)).query
              (Key.later message challenge key)) >>= pure) 1
          exact ⟨by omega, fun _ => trivial⟩)
    have hb := isTotalQueryBound_bind h (fun path => show IsTotalQueryBound
      (pure (⟨message, ⟨challenge, path⟩⟩ : (protocol (round :: rounds)).tree.ExecutionPath) :
        OracleComp (Spec Input (round :: rounds)) _) 0 from trivial)
    simpa only [Nat.mul_one, Nat.add_zero, protocol, Protocol.oracleWith, Protocol.public] using hb

def completedPath {Input : Type} : (rounds : List Round) → Input →
    Messages rounds → Table Input rounds → (protocol rounds).tree.ExecutionPath
  | [], _, _, _ => PUnit.unit
  | _ :: rounds, z, (message, messages), table =>
    let challenge := table (Key.here z message)
    ⟨message, ⟨challenge,
      completedPath rounds z messages (fun key => table (Key.later message challenge key))⟩⟩

def completionKeys {Input : Type} : (rounds : List Round) → Input →
    Messages rounds → Table Input rounds → List (Key Input rounds)
  | [], _, _, _ => []
  | _ :: rounds, z, (message, messages), table =>
    let challenge := table (Key.here z message)
    Key.here z message ::
      (completionKeys rounds z messages (fun key => table (Key.later message challenge key))).map
        (Key.later message challenge)

theorem complete_eval {Input : Type} (rounds : List Round) (z : Input)
    (messages : Messages rounds) (table : Table Input rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds z messages) =
      completedPath rounds z messages table := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
    rcases messages with ⟨message, messages⟩
    simp only [complete, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply, evalWithAnswerFn_simulateQ, prependQuery, completedPath]
    exact congrArg (fun path => (⟨message, ⟨table (Key.here z message), path⟩⟩ :
      (protocol (round :: rounds)).tree.ExecutionPath))
      (ih messages (fun key => table (Key.later message (table (Key.here z message)) key)))

theorem complete_log_keys {Input : Type} (rounds : List Round) (z : Input)
    (messages : Messages rounds) (table : Table Input rounds) :
    (tableQueryLog (complete rounds z messages) table).map Sigma.fst =
      completionKeys rounds z messages table := by
  induction rounds with
  | nil => simp [complete, completionKeys, protocol, Protocol.done]
  | cons round rounds ih =>
    rcases messages with ⟨message, messages⟩
    simp only [complete, protocol, Protocol.oracleWith, Protocol.public, tableQueryLog_bind,
      tableQueryLog_pure, List.append_nil, tableQueryLog_simulateQ, prependQuery,
      evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, tableQueryLog_query,
      List.singleton_append, List.map_cons, ← List.map_eq_flatMap, List.map_map,
      Function.comp_def, completionKeys]
    congr 1
    simpa only [List.flatMap_singleton, List.map_map, Function.comp_def] using
      congrArg (List.map (Key.later message (table (Key.here z message))))
        (ih messages (fun key => table (Key.later message (table (Key.here z message)) key)))

theorem completionKeys_input {Input : Type} (rounds : List Round) (z : Input)
    (messages : Messages rounds) (table : Table Input rounds) (key : Key Input rounds)
    (queried : key ∈ completionKeys rounds z messages table) : key.input = z := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
    rcases messages with ⟨message, messages⟩
    rcases List.mem_cons.mp queried with first | later
    · subst key; rfl
    · obtain ⟨suffixKey, inSuffix, rfl⟩ := List.mem_map.mp later
      exact ih messages _ suffixKey inSuffix

def execution {Input W : Type} (rounds : List Round)
    (adversary : OracleComp (Spec Input rounds) (Input × Messages rounds × W)) :
    OracleComp (Spec Input rounds) (Input × (protocol rounds).tree.ExecutionPath × W) := do
  let (z, messages, witness) ← adversary
  let path ← complete rounds z messages
  pure (z, path, witness)

theorem execution_queryBound {Input W : Type} (rounds : List Round)
    (adversary : OracleComp (Spec Input rounds) (Input × Messages rounds × W))
    (Q : Nat) (bounded : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (execution rounds adversary) (Q + rounds.length) := by
  apply isTotalQueryBound_bind bounded
  rintro ⟨z, messages, witness⟩
  have h := isTotalQueryBound_bind (complete_queryBound rounds z messages)
    (fun path => show IsTotalQueryBound
      (pure (z, path, witness) : OracleComp (Spec Input rounds) _) 0 from trivial)
  simpa only [Nat.add_zero] using h

end ZkcSecurity.ArkLib.FiatShamir.Transcript
