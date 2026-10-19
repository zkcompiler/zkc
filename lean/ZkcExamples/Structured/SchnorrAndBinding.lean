module

public import ZkcExamples.Structured.SchnorrAnd
public import Zkc.Protocols.Schnorr

@[expose] public section

/-! The authored `knowledge` target of `sigma::SchnorrAnd`: the retained
`DLogPair` formula with two witness ports. The binding, the formula's process
and the observed decision are the generated ones of `SchnorrAndNormalForms`.
Each witness is keyed by its own selector, so two extracted witnesses are
independent logical values; nothing identifies them with each other or with the
prover's inputs. Below: the transcript-pair view of the observed boundary used
by the Σ-protocol consumers, and this protocol's mathematics (extraction and
honest acceptance). -/
namespace ZkcExamples.Structured.SchnorrAndBinding
open Zkc.Source Zkc.Source.Structured SchnorrAndViews

set_option smartUnfolding false

abbrev decisionSelector : BoundarySelector SchnorrAndNormalForms.owner.protocol.signature .boolean :=
  SchnorrAndNormalForms.decisionSelector

/-- The two witness selectors name different prover input ports, so their
logical slots are distinct. -/
theorem witnesses_distinct :
    SchnorrAndNormalForms.firstWitnessSelector.erase ≠ SchnorrAndNormalForms.secondWitnessSelector.erase := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The target denotes the actual retained formula process. -/
abbrev Relation (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) : Prop :=
  SchnorrAndNormalForms.Relation firstBase firstKey secondBase secondKey firstWitness secondWitness

theorem relation_iff (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    Relation firstBase firstKey secondBase secondKey firstWitness secondWitness ↔
      firstKey = firstWitness • firstBase ∧ secondKey = secondWitness • secondBase :=
  SchnorrAndNormalForms.relation_iff firstBase firstKey secondBase secondKey firstWitness secondWitness

/-- Only the verifier's own inputs and its actual returned tuple are projected,
for one transcript given as its pair of commitments, challenge and pair of
responses. An adversarial transcript does not imply an honest prover execution. -/
abbrev observedBoundary (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) :
    ContractBoundaryValues SchnorrAndNormalForms.owner F G :=
  SchnorrAndNormalForms.observedBoundary firstBase firstKey secondBase secondKey service
    commitments.1 commitments.2 challenge responses.1 responses.2

/-- The selected decision is the actual verifier's: both equations must hold. -/
theorem observed_accepts_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge responses) = some true ↔
      responses.1 • firstBase = commitments.1 + challenge • firstKey ∧
        responses.2 • secondBase = commitments.2 + challenge • secondKey :=
  SchnorrAndNormalForms.observed_accepts_iff firstBase firstKey secondBase secondKey service
    commitments.1 commitments.2 challenge responses.1 responses.2

theorem observed_target_iff (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (service : Nat) (commitments : G × G) (challenge : F) (responses : F × F) :
    (SchnorrAndNormalForms.target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey
        secondBase secondKey service commitments challenge responses)
        (SchnorrAndNormalForms.assignments firstBase secondBase firstWitness secondWitness) ↔
      Relation firstBase firstKey secondBase secondKey firstWitness secondWitness :=
  SchnorrAndNormalForms.observed_target_iff firstBase firstKey secondBase secondKey service
    firstWitness secondWitness commitments.1 commitments.2 challenge responses.1 responses.2

/-- Two transcripts with one pair of commitments and distinct challenges, both
accepted by the actual verifier, give a witness pair for the actual target at
the first transcript's returned boundary. The pair is new; it is no prover input. -/
theorem extracted_target (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (first second : F) (firstResponses secondResponses : F × F)
    (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments first firstResponses) = some true)
    (acceptSecond : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments second secondResponses) = some true) :
    (SchnorrAndNormalForms.target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey
        secondBase secondKey service commitments first firstResponses)
      (SchnorrAndNormalForms.assignments firstBase secondBase
        ((firstResponses.1 - secondResponses.1) / (first - second))
        ((firstResponses.2 - secondResponses.2) / (first - second))) := by
  rw [observed_accepts_iff] at acceptFirst acceptSecond
  apply (observed_target_iff ..).mpr
  apply (relation_iff ..).mpr
  exact ⟨(Zkc.Protocols.Schnorr.extract_public_key firstBase firstKey commitments.1 first second
      firstResponses.1 secondResponses.1 distinct acceptFirst.1 acceptSecond.1).symm,
    (Zkc.Protocols.Schnorr.extract_public_key secondBase secondKey commitments.2 first second
      firstResponses.2 secondResponses.2 distinct acceptFirst.2 acceptSecond.2).symm⟩

/-- The values the admitted prover sends (`SchnorrAnd.prover_run`) for given
nonces and a challenge, delivered with that challenge, are accepted by the
actual verifier when both keys use the witnesses at the verifier's bases. This
states the values, not a joint run of the two participants. -/
theorem honest_accepts (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (firstNonce secondNonce challenge : F) (service : Nat)
    (valid : Relation firstBase firstKey secondBase secondKey firstWitness secondWitness) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
      (firstNonce • firstBase, secondNonce • secondBase) challenge
      (firstNonce + challenge * firstWitness, secondNonce + challenge * secondWitness)) = some true := by
  obtain ⟨firstValid, secondValid⟩ := (relation_iff ..).mp valid
  apply (observed_accepts_iff ..).mpr
  subst firstValid secondValid
  exact ⟨Zkc.Protocols.Schnorr.response_equation .., Zkc.Protocols.Schnorr.response_equation ..⟩

end ZkcExamples.Structured.SchnorrAndBinding
