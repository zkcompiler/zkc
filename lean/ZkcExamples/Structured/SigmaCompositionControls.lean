module

public import ZkcExamples.Structured.SigmaLogicalContexts
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

/-! Controls for the imported Schnorr AND and Chaum–Pedersen protocols.

The extraction premises are satisfiable: honest transcripts for one nonce
choice and two distinct challenges, with the values the admitted provers send,
are accepted by the actual verifiers, and extraction returns the honest
witnesses. Over the rationals with bases one and keys zero and one, the AND
verifier accepts two transcripts that share their commitments and differ in the
challenge, although no single witness exists: a shared challenge does not make
the witnesses shared. For that statement the Chaum–Pedersen verifier accepts
single transcripts but no such pair. -/
namespace ZkcExamples.Structured.SigmaCompositionControls
open Zkc.Source Zkc.Source.Structured SigmaLogicalContexts

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ### Satisfiable extraction premises -/

/-- Honest Chaum–Pedersen transcripts at challenges zero and one satisfy the
extraction premises, and the shared binder value extracted from them is the
prover's witness. -/
theorem equality_premises (firstBase secondBase : G) (witness nonce : F) (service : Nat) :
    ChaumPedersenBinding.decisionSelector.read {} (ChaumPedersenBinding.observedBoundary firstBase
        (witness • firstBase) secondBase (witness • secondBase) service
        (nonce • firstBase, nonce • secondBase) 0 (nonce + 0 * witness)) = some true ∧
      ChaumPedersenBinding.decisionSelector.read {} (ChaumPedersenBinding.observedBoundary firstBase
        (witness • firstBase) secondBase (witness • secondBase) service
        (nonce • firstBase, nonce • secondBase) 1 (nonce + 1 * witness)) = some true ∧
      ((nonce + 0 * witness) - (nonce + 1 * witness)) / (0 - 1) = witness := by
  have valid : ChaumPedersenBinding.Relation firstBase (witness • firstBase) secondBase
      (witness • secondBase) witness := (ChaumPedersenBinding.relation_iff ..).mpr ⟨rfl, rfl⟩
  exact ⟨ChaumPedersenBinding.honest_accepts _ _ _ _ _ _ _ _ valid,
    ChaumPedersenBinding.honest_accepts _ _ _ _ _ _ _ _ valid, by simp⟩

/-- Honest AND transcripts at challenges zero and one satisfy the extraction
premises, and the extracted pair is the prover's pair of witnesses. -/
theorem pair_premises (firstBase secondBase : G) (firstWitness secondWitness firstNonce secondNonce : F)
    (service : Nat) :
    SchnorrAndBinding.decisionSelector.read {} (SchnorrAndBinding.observedBoundary firstBase
        (firstWitness • firstBase) secondBase (secondWitness • secondBase) service
        (firstNonce • firstBase, secondNonce • secondBase) 0
        (firstNonce + 0 * firstWitness, secondNonce + 0 * secondWitness)) = some true ∧
      SchnorrAndBinding.decisionSelector.read {} (SchnorrAndBinding.observedBoundary firstBase
        (firstWitness • firstBase) secondBase (secondWitness • secondBase) service
        (firstNonce • firstBase, secondNonce • secondBase) 1
        (firstNonce + 1 * firstWitness, secondNonce + 1 * secondWitness)) = some true ∧
      ((firstNonce + 0 * firstWitness) - (firstNonce + 1 * firstWitness)) / (0 - 1) = firstWitness ∧
      ((secondNonce + 0 * secondWitness) - (secondNonce + 1 * secondWitness)) / (0 - 1) = secondWitness := by
  have valid : SchnorrAndBinding.Relation firstBase (firstWitness • firstBase) secondBase
      (secondWitness • secondBase) firstWitness secondWitness :=
    (SchnorrAndBinding.relation_iff ..).mpr ⟨rfl, rfl⟩
  exact ⟨SchnorrAndBinding.honest_accepts _ _ _ _ _ _ _ _ _ _ valid,
    SchnorrAndBinding.honest_accepts _ _ _ _ _ _ _ _ _ _ valid, by simp,
    by simp⟩

/-! ### A shared challenge does not share witnesses -/

/-- Over the rationals, with both bases one and keys zero and one, the actual
AND verifier accepts two transcripts with the same commitments and challenges
zero and one. Their extracted pair satisfies the independent context, while no
single binder value satisfies the shared context at the same ports. -/
theorem pair_accepts_without_common_witness (service : Nat) :
    SchnorrAndBinding.decisionSelector.read {} (SchnorrAndBinding.observedBoundary (1 : ℚ) 0 1 1 service
        (0, 0) (0 : ℚ) (0, 0)) = some true ∧
      SchnorrAndBinding.decisionSelector.read {} (SchnorrAndBinding.observedBoundary (1 : ℚ) 0 1 1 service
        (0, 0) (1 : ℚ) (0, 1)) = some true ∧
      IndependentHolds (SchnorrAndBinding.observedBoundary (1 : ℚ) 0 1 1 service (0, 0) (0 : ℚ) (0, 0))
        0 1 ∧
      ¬ ∃ witness : ℚ, PairShared (SchnorrAndBinding.observedBoundary (1 : ℚ) 0 1 1 service (0, 0)
        (0 : ℚ) (0, 0)) witness := by
  refine ⟨(SchnorrAndBinding.observed_accepts_iff ..).mpr (by norm_num),
    (SchnorrAndBinding.observed_accepts_iff ..).mpr (by norm_num),
    (independent_iff ..).mpr ((SchnorrAndBinding.relation_iff ..).mpr (by norm_num)), ?_⟩
  rintro ⟨witness, shared⟩
  have equations := (pairShared_iff ..).mp shared
  have zero : (0 : ℚ) = witness := by simpa using equations.1
  have one : (1 : ℚ) = witness := by simpa using equations.2
  exact zero_ne_one (zero.trans one.symm)

/-- For the same statement, the actual Chaum–Pedersen verifier accepts a single
transcript, but no pair of transcripts with common commitments and distinct
challenges: their shared extraction would be a common witness. -/
theorem equality_accepts_no_pair_without_common_witness (service : Nat) (commitments : ℚ × ℚ)
    (first second firstResponse secondResponse : ℚ) (distinct : first ≠ second) :
    ChaumPedersenBinding.decisionSelector.read {} (ChaumPedersenBinding.observedBoundary (1 : ℚ) 0 1 1
        service (0, 0) (0 : ℚ) (0 : ℚ)) = some true ∧
    ¬ (ChaumPedersenBinding.decisionSelector.read {} (ChaumPedersenBinding.observedBoundary (1 : ℚ) 0 1 1
        service commitments first firstResponse) = some true ∧
      ChaumPedersenBinding.decisionSelector.read {} (ChaumPedersenBinding.observedBoundary (1 : ℚ) 0 1 1
        service commitments second secondResponse) = some true) := by
  refine ⟨(ChaumPedersenBinding.observed_accepts_iff ..).mpr (by norm_num), ?_⟩
  rintro ⟨acceptFirst, acceptSecond⟩
  have shared := shared_extraction (1 : ℚ) 0 1 1 service commitments first second firstResponse
    secondResponse distinct acceptFirst acceptSecond
  have equations := (ChaumPedersenBinding.relation_iff ..).mp ((shared_iff ..).mp shared)
  have zero : (0 : ℚ) = (firstResponse - secondResponse) / (first - second) := by simpa using equations.1
  have one : (1 : ℚ) = (firstResponse - secondResponse) / (first - second) := by simpa using equations.2
  exact zero_ne_one (zero.trans one.symm)

end ZkcExamples.Structured.SigmaCompositionControls
