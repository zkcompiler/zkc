module

public import Zkc.Protocols.Sumcheck.Polynomial
public import ArkLib.Interaction.Oracle.Security.StateRestorationGame
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

@[expose] public section

set_option autoImplicit false

/-! All-authored-prefix knowledge certificates for finite quadratic Sumcheck.
The witness is a unit token: its predicate is residual correctness and every
prior boundary check. The existential witness remains inside `badChallenge`.
-/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir

open Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open OracleComp OracleSpec
open Zkc.Polynomial Zkc.Protocols.AlgebraicRounds
open Zkc.Protocols.Sumcheck (collision_card)

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

instance finiteMessage : Finite (Message F) :=
  Finite.of_injective (fun m : Message F => (m.constant, m.linear, m.quadratic))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; cases h; rfl)

/-- The whole coefficient triple is the prover message at one logical round. -/
@[instance_reducible] def messageInterface : OracleInterface (Message F) where
  Query := Unit
  toOC := { spec := fun _ => Message F, impl := fun _ message => message }

@[implicit_reducible] def round : Round where
  Message := Message F
  Challenge := F
  interface := messageInterface
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : Nat → List Round
  | 0 => []
  | n + 1 => round (F := F) :: rounds n

@[simp] theorem rounds_length (n : Nat) : (rounds (F := F) n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/-- No knowledge is manufactured by discarding a failed earlier check. -/
def residualState {n : Nat} (priorChecks : Prop) (p : Quadratic F n) (claim : F) :
    KnowledgeState := ⟨Unit, fun _ => priorChecks ∧ claim = p.booleanSum⟩

/-- Each message adds its boundary check; each challenge restricts the actual
public polynomial. Every backward map is the identity on unit witnesses. -/
def extractor : (n : Nat) → (priorChecks : Prop) → (p : Quadratic F n) → (claim : F) →
    RoundExtractor (protocol (rounds (F := F) n)).tree (residualState priorChecks p claim)
  | 0, _, _, _ => PUnit.unit
  | n + 1, priorChecks, p, claim => fun message =>
      ⟨residualState (priorChecks ∧ message.boundary = claim) p claim, id,
        fun challenge =>
          ⟨residualState (priorChecks ∧ message.boundary = claim)
            (p.restrict challenge) (message.evaluate challenge), id,
            extractor n (priorChecks ∧ message.boundary = claim)
              (p.restrict challenge) (message.evaluate challenge)⟩⟩

/-- Prover preservation is proved for arbitrary prior checks, claims, and messages. -/
theorem prover_preserving (n : Nat) (priorChecks : Prop) (p : Quadratic F n) (claim : F) :
    (extractor n priorChecks p claim).IsProverPreserving (protocol (rounds n)).roles := by
  induction n generalizing priorChecks claim with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · intro message witness known
        exact ⟨known.1.1, known.2⟩
      · intro message
        refine ⟨?_, fun challenge => ih _ _ _⟩
        intro challenge sender
        cases sender

/-- Exact existential-event identification, with no fixed-witness relaxation. -/
theorem badChallenge_iff {n : Nat} (priorChecks : Prop) (p : Quadratic F (n + 1))
    (claim : F) (message : Message F) (challenge : F) :
    RoundExtractor.badChallenge (extractor (n + 1) priorChecks p claim message).2.2 challenge ↔
      priorChecks ∧ message.boundary = claim ∧ claim ≠ p.booleanSum ∧
        message.evaluate challenge = (p.restrict challenge).booleanSum := by
  change (∃ _ : Unit, ¬ ((priorChecks ∧ message.boundary = claim) ∧ claim = p.booleanSum) ∧
    (priorChecks ∧ message.boundary = claim) ∧
      message.evaluate challenge = (p.restrict challenge).booleanSum) ↔ _
  constructor
  · rintro ⟨_, before, ⟨prior, boundary⟩, after⟩
    exact ⟨prior, boundary, fun same => before ⟨⟨prior, boundary⟩, same⟩, after⟩
  · rintro ⟨prior, boundary, different, after⟩
    exact ⟨(), fun before => different before.2, ⟨prior, boundary⟩, after⟩

/-- At most two repairs at every authored prefix, including unreachable prefixes. -/
theorem badChallenge_card {n : Nat} (priorChecks : Prop) (p : Quadratic F (n + 1))
    (claim : F) (message : Message F) :
    letI := Classical.propDecidable
    (Finset.univ.filter fun challenge : F => RoundExtractor.badChallenge
      (extractor (n + 1) priorChecks p claim message).2.2 challenge).card ≤ 2 := by
  classical
  simp only [badChallenge_iff]
  by_cases prior : priorChecks
  · by_cases boundary : message.boundary = claim
    · by_cases correct : claim = p.booleanSum
      · simp [correct]
      · simpa [prior, boundary, correct] using
          collision_card message p (boundary ▸ correct)
    · simp [boundary]
  · simp [prior]

/-- The actual ArkLib local event bound, quantified over every prefix. -/
theorem locally_bounded (n : Nat) (priorChecks : Prop) (p : Quadratic F n) (claim : F) :
    RoundExtractor.IsLocallyBounded (extractor n priorChecks p claim)
      (protocol (rounds n)).roles
      (uniformSchedule (2 / (Fintype.card F : ENNReal)) (rounds n)) := by
  classical
  induction n generalizing priorChecks claim with
  | zero => trivial
  | succ n ih =>
      intro message
      refine ⟨?_, fun challenge => ih _ _ _⟩
      apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
      intro round context
      change Pr{let challenge ← $ᵗ F}[
        RoundExtractor.badChallenge (extractor (n + 1) priorChecks p claim message).2.2
          challenge] ≤ 2 / (Fintype.card F : ENNReal)
      exact (SampleableType.prEvent_uniformSample_le_div_iff _).mpr
        (badChallenge_card priorChecks p claim message)

/-- A fully discharged certificate, rather than an assumed local-security field. -/
noncomputable def knowledgeCertificate (n : Nat) (priorChecks : Prop) (p : Quadratic F n) (claim : F) :
    KnowledgeCertificate (protocol (rounds (F := F) n)).tree
      (protocol (rounds (F := F) n)).roles (residualState priorChecks p claim) where
  extractor := extractor n priorChecks p claim
  challenges := uniformSchedule (2 / (Fintype.card F : ENNReal)) (rounds n)
  prover_preserving := prover_preserving n priorChecks p claim
  local_bound := locally_bounded n priorChecks p claim

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir
