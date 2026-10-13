module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.EarlyStop
public import Zkc.Protocols.Sumcheck.NativeConstruction
public import Zkc.Semantics.MonadExecution

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The constructed native subject runs against the same full-prefix oracle as
its adversary. The selected output fixes source/construction/schedule identity;
queries to every other binding remain available to the adversary. -/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native

open Interaction.Oracle.Security
open OracleComp OracleSpec
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Protocols.Sumcheck.Common
open Zkc.Protocols.Sumcheck
open Zkc.Protocols.Sumcheck.NativeConstruction
open Zkc.Source

variable {Context F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

deriving instance DecidableEq for Binding

abbrev Oracle (Context F : Type) [Field F] [DecidableEq F] [Fintype F] [SampleableType F] :=
  FullPrefix.Oracle (Binding Context F) F

/-- The adversary chooses a statement and messages after its oracle accesses. -/
structure Selection (Context F : Type) where
  context : Context
  coefficients : Coefficients F
  claim : F
  first : Message F
  second : Message F

abbrev Adversary (Context F : Type) [Field F] [DecidableEq F] [Fintype F] [SampleableType F] :=
  OracleComp (Oracle Context F) (Selection Context F)

def binding (source construction : String) (schedule : Schedule) (choice : Selection Context F) :
    Binding Context F :=
  ⟨source, construction, choice.context, schedule, choice.coefficients, choice.claim⟩

def statement (b : Binding Context F) : Statement F := ⟨b.coefficients, b.claim⟩

/-- Each reached request produces one reply and logs its exact full key. -/
def queryHandler : PIR.MonadHandler (OracleComp (Oracle Context F))
    (oracleSignature Context F) Unit (QueryKey Context F) := fun key state => do
  let value : F ← liftM ((Oracle Context F).query key)
  pure ⟨.returned value, state, [key]⟩

abbrev Record (Context F : Type) :=
  PIR.Execution Unit (QueryKey Context F) (Values (Value Context F) outputTypes)

/-- Only a returned true result counts as acceptance; every inner stop rejects. -/
def acceptedRecord (record : Record Context F) : Bool :=
  match record.outcome with
  | .stopped _ => false
  | .returned reply => (result reply).getD false

/-- Acceptance projection is performed only after running the full process with
its returned transcript, stop reason, handler state and reached query log. -/
theorem experiment_observation (b : Binding Context F) (proof : Message F × Message F) :
    acceptedRecord <$> (NativeConstruction.experiment b proof).runM queryHandler () =
      FullPrefix.earlyVerify statement b proof.1 proof.2 := by
  by_cases first : wireBoundary proof.1 = b.claim
  · simp only [NativeConstruction.experiment, first, decide_true, ↓reduceIte, PIR.Proc.runM,
      queryHandler, bind_assoc, pure_bind, PIR.Execution.followM,
      map_eq_pure_bind, FullPrefix.earlyVerify, statement]
    apply bind_congr
    intro challenge
    by_cases second : wireBoundary proof.2 = wireEvaluate proof.1 challenge
    · simp [second, PIR.Proc.runM, queryHandler, PIR.Execution.followM,
        acceptedRecord, result]
    · simp [second, PIR.Proc.runM, acceptedRecord]
  · simp [NativeConstruction.experiment, first, PIR.Proc.runM, acceptedRecord,
      FullPrefix.earlyVerify, statement]

/-- A subject has the exact native typed reply, including its final transcript. -/
abbrev Subject (Context F : Type) :=
  Selection Context F → PIR.Proc (oracleSignature Context F) (Values (Value Context F) outputTypes)

def reference (source construction : String) (schedule : Schedule) : Subject Context F :=
  fun choice => NativeConstruction.experiment (binding source construction schedule choice) (choice.first, choice.second)

/-- This game executes the actual supplied process; it does not complete rejected runs. -/
def game (source construction : String) (schedule : Schedule) (subject : Subject Context F)
    (adversary : Adversary Context F) : OracleComp (Oracle Context F) (Binding Context F × Record Context F) := do
  let choice ← adversary
  let record ← (subject choice).runM queryHandler ()
  pure (binding source construction schedule choice, record)

def selectedAdversary (source construction : String) (schedule : Schedule)
    (adversary : Adversary Context F) : FullPrefix.Adversary (Binding Context F) F :=
  (fun choice => (binding source construction schedule choice, choice.first, choice.second, ())) <$>
    adversary

/-- A full denotation equation transports the entire experiment, before any
acceptance projection. The equation must be proved for the actual imported body. -/
theorem game_eq (source construction : String) (schedule : Schedule)
    (subject : Subject Context F)
    (denotation : ∀ choice, subject choice = reference source construction schedule choice)
    (adversary : Adversary Context F) :
    game source construction schedule subject adversary =
      game source construction schedule (reference source construction schedule) adversary := by
  have same : subject = reference source construction schedule := funext denotation
  rw [same]

/-- The native execution observation is precisely the early-stop oracle game. -/
theorem game_observation (source construction : String) (schedule : Schedule)
    (adversary : Adversary Context F) :
    (fun result => (result.1, acceptedRecord result.2)) <$>
      game source construction schedule (reference source construction schedule) adversary =
    FullPrefix.earlyGame statement (selectedAdversary source construction schedule adversary) := by
  simp only [game, selectedAdversary, FullPrefix.earlyGame, map_eq_pure_bind,
    bind_assoc, pure_bind]
  apply bind_congr
  intro choice
  have observation := experiment_observation
    (binding source construction schedule choice) (choice.first, choice.second)
  simpa only [reference, map_eq_pure_bind, bind_assoc, pure_bind] using
    congrArg (fun p => (fun accepted => (binding source construction schedule choice, accepted)) <$> p)
      observation

/-- The selected actual process consumes at most two further requests. -/
theorem game_queryBound (source construction : String) (schedule : Schedule)
    (subject : Subject Context F)
    (denotation : ∀ choice, subject choice = reference source construction schedule choice)
    (adversary : Adversary Context F) (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (game source construction schedule subject adversary) (Q + 2) := by
  rw [game_eq source construction schedule subject denotation]
  apply (isQueryBound_iff_of_map_eq (game_observation source construction schedule adversary)
    (fun _ b => 0 < b) (fun _ b => b - 1)).mpr
  apply FullPrefix.earlyGame_queryBound
  simpa only [selectedAdversary, IsTotalQueryBound, isQueryBound_map_iff] using queryBound

variable [DecidableEq Context]

/-- Actual full-denotation consumers discharge only the body equation. Every
Sumcheck residual, existential bad-event, simulation and early-stop premise has
already been proved. Arbitrary adaptive queries to other bindings remain allowed. -/
theorem soundness (source construction : String) (schedule : Schedule)
    (subject : Subject Context F)
    (denotation : ∀ choice, subject choice = reference source construction schedule choice)
    (adversary : Adversary Context F) (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let output ← (simulateQ randomOracle
      (game source construction schedule subject adversary)).run' ∅}[
      acceptedRecord output.2 = true ∧
        output.1.claim ≠ (polynomial output.1.coefficients).booleanSum] ≤
          (Q + 3 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  rw [game_eq source construction schedule subject denotation]
  have bound := FullPrefix.early_soundness statement
    (selectedAdversary source construction schedule adversary) Q
    (by simpa only [selectedAdversary, IsTotalQueryBound, isQueryBound_map_iff] using queryBound)
  rw [← game_observation, simulateQ_map] at bound
  simpa only [StateT.run'_map', prEvent_map, statement] using bound

/-- Independently sampled private coins select adaptive adversaries with a
common all-branch budget; each run begins with the same empty cache. -/
theorem randomized_soundness (source construction : String) (schedule : Schedule)
    (subject : Subject Context F)
    (denotation : ∀ choice, subject choice = reference source construction schedule choice)
    {Coins : Type} (coins : ProbComp Coins) (adversary : Coins → Adversary Context F)
    (Q : Nat) (queryBound : ∀ coin, IsTotalQueryBound (adversary coin) Q) :
    Pr{let output ← (coins >>= fun coin => (simulateQ randomOracle
      (game source construction schedule subject (adversary coin))).run' ∅)}[
      acceptedRecord output.2 = true ∧
        output.1.claim ≠ (polynomial output.1.coefficients).booleanSum] ≤
          (Q + 3 : ENNReal) * (2 / (Fintype.card F : ENNReal)) :=
  prEvent_bind_le_of_forall_le coins _ _
    (fun coin => soundness source construction schedule subject denotation
      (adversary coin) Q (queryBound coin))

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native
