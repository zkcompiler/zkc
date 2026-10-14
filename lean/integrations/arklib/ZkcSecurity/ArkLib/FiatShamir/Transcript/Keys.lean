module

/-
Knowledge-state projection adapted from ArkLib StateRestoration.lean.
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in ArkLib's LICENSE file.
Original author: Quang Dao.
-/

public import ArkLib.Interaction.Oracle.Security.StateRestoration

@[expose] public section

/-! Full-prefix keys for a finite list of heterogeneous public-coin rounds.

The protocol tree and knowledge interfaces are ArkLib's existing ones. Unlike
restoration keys, a later key explicitly retains every preceding challenge.
Every well-typed prefix is queryable, including inconsistent and unreachable
ones. Probability models use classical key equality; this is not a byte codec.
-/

namespace ZkcSecurity.ArkLib.FiatShamir.Transcript
open Interaction.Oracle Interaction.Oracle.Security
open StateRestoration (Round protocol uniformSchedule)
open OracleComp OracleSpec

def Key (Input : Type) : List Round → Type
  | [] => Empty
  | round :: rounds => (Input × round.Message) ⊕
      (round.Message × round.Challenge × Key Input rounds)

namespace Key
variable {Input : Type}

@[match_pattern, reducible] def here {round : Round} {rounds : List Round}
    (z : Input) (message : round.Message) : Key Input (round :: rounds) := .inl (z, message)

@[match_pattern, reducible] def later {round : Round} {rounds : List Round}
    (message : round.Message) (challenge : round.Challenge) (key : Key Input rounds) :
    Key Input (round :: rounds) := .inr (message, challenge, key)

noncomputable instance instDecidableEq (rounds : List Round) : DecidableEq (Key Input rounds) :=
  Classical.decEq _

def input : {rounds : List Round} → Key Input rounds → Input
  | [], key => nomatch key
  | _ :: _, .inl (z, _) => z
  | _ :: _, .inr (_, _, key) => key.input

@[reducible] def Challenge : {rounds : List Round} → Key Input rounds → Type
  | [], key => nomatch key
  | round :: _, .inl _ => round.Challenge
  | _ :: _, .inr (_, _, key) => key.Challenge

def remaining : {rounds : List Round} → Key Input rounds → List Round
  | [], key => nomatch key
  | _ :: rounds, .inl _ => rounds
  | _ :: _, .inr (_, _, key) => key.remaining

instance {rounds : List Round} (key : Key Input rounds) : Finite key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
    cases key with
    | inl _ => exact round.finiteChallenge
    | inr data => exact ih data.2.2

instance {rounds : List Round} (key : Key Input rounds) : Nonempty key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
    cases key with
    | inl _ => exact round.nonemptyChallenge
    | inr data => exact ih data.2.2

instance {rounds : List Round} (key : Key Input rounds) : SampleableType key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
    cases key with
    | inl _ => exact round.sampleChallenge
    | inr data => exact ih data.2.2

end Key

abbrev Spec (Input : Type) (rounds : List Round) : OracleSpec (Key Input rounds) :=
  OracleSpec.ofFn Key.Challenge

abbrev Table (Input : Type) (rounds : List Round) :=
  (key : Key Input rounds) → key.Challenge

universe w

/-- An explicit prior challenge selects the next extractor directly. No table
lookup can change the knowledge state before the key's own challenge. -/
def keyExtractor {Input : Type} : {rounds : List Round} → {state : KnowledgeState.{w}} →
    RoundExtractor (protocol rounds).tree state → (key : Key Input rounds) →
    (before : KnowledgeState.{w}) ×
      RoundExtractor (.public key.Challenge (fun _ => (protocol key.remaining).tree)) before
  | [], _, _, key => nomatch key
  | _ :: _, _, extractor, .inl (_, message) =>
      ⟨(extractor message).1, (extractor message).2.2⟩
  | _ :: _, _, extractor, .inr (message, challenge, key) =>
      keyExtractor ((extractor message).2.2 challenge).2.2 key

/-- The all-prefix local knowledge premise covers arbitrary authored prefixes. -/
theorem keyExtractor_local_bound {Input : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (error : ENNReal)
    (bounded : RoundExtractor.IsLocallyBounded extractor (protocol rounds).roles
      (uniformSchedule error rounds)) (key : Key Input rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      RoundExtractor.badChallenge (keyExtractor extractor key).2 response] ≤ error := by
  induction rounds generalizing state with
  | nil => exact key.elim
  | cons round rounds ih =>
    cases key with
    | inl data =>
      rcases data with ⟨z, message⟩
      exact ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp (bounded message).1) () ()
    | inr data =>
      rcases data with ⟨message, challenge, key⟩
      exact ih ((extractor message).2.2 challenge).2.2 ((bounded message).2 challenge) key

end ZkcSecurity.ArkLib.FiatShamir.Transcript
