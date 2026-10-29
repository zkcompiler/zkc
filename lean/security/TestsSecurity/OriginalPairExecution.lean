module

public import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
public import ZkcExamples.Structured.Generated.Connections.TwoSums
public import Zkc.Construction.OriginalCorrespondence

@[expose] public section

/-! Pair execution through the maintained generated roots. Arbitrary physical
rows include malformed ABI inputs. The existing runtime retains every return,
proof suffix, observation and oracle/private-service state; a stopped producer
skips validation. No source-shape or honest-input premise restricts this test. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
noncomputable section
attribute [local implicit_reducible] Zkc.Source.Structured.CheckedProtocol.signature
namespace TestsSecurity.OriginalPairExecution
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Connections

namespace Small
open SmallSumcheck

theorem execute_pair (model : DomainModel)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S) :
    Domain.executePair model program context producerArtifact validatorArtifact
      producerInputs validatorInputs oracle state services =
      (do
        let original ← Domain.run .producer oracle
          (producerFacts.simulation model producerInputs).paired
          ⟨producerInputs, [], state⟩ services
        let produced := Original.mapExecution Prod.snd original
        match produced.outcome with
        | .stopped _ => pure ⟨produced, none⟩
        | .returned _ =>
            let original ← Domain.run .validator oracle
              (validatorFacts.simulation model validatorInputs).paired
              ⟨validatorInputs, produced.state.proof, produced.state.oracle⟩ services
            pure ⟨produced, some (Original.mapExecution Prod.snd original)⟩) := by
  have producerLaw := (producerFacts.simulation model producerInputs).runM
    (Domain.handler .producer oracle services) ⟨producerInputs, [], state⟩
  have validatorLaw := fun proof final => (validatorFacts.simulation model validatorInputs).runM
    (Domain.handler .validator oracle services) ⟨validatorInputs, proof, final⟩
  unfold Domain.executePair Domain.produce Domain.validate Domain.run
  erw [producerLaw]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext original
  cases outcome : (Original.mapExecution Prod.snd original).outcome with
  | stopped => rfl
  | returned =>
    erw [validatorLaw]
    simp only [bind_assoc, pure_bind]

/-- Validation also preserves an arbitrary supplied unread proof suffix. -/
theorem validate (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (proof : Domain.Proof model.toCarriers) (oracle : Domain.Oracle m model.toCarriers S)
    (state : S) (services : Domain.LocalServices m model.toCarriers S) :
    Domain.validate model program context validatorArtifact physical proof oracle state services =
      (do let execution ← Domain.run .validator oracle
            (validatorFacts.simulation model physical).paired ⟨physical, proof, state⟩ services
          pure (Original.mapExecution Prod.snd execution)) :=
  (validatorFacts.simulation model physical).runM
    (Domain.handler .validator oracle services) ⟨physical, proof, state⟩

#print axioms execute_pair
#print axioms validate
end Small

namespace Two
open TwoSums

theorem execute_pair (model : DomainModel)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S) :
    Domain.executePair model program context producerArtifact validatorArtifact
      producerInputs validatorInputs oracle state services =
      (do
        let original ← Domain.run .producer oracle
          (producerFacts.simulation model producerInputs).paired
          ⟨producerInputs, [], state⟩ services
        let produced := Original.mapExecution Prod.snd original
        match produced.outcome with
        | .stopped _ => pure ⟨produced, none⟩
        | .returned _ =>
            let original ← Domain.run .validator oracle
              (validatorFacts.simulation model validatorInputs).paired
              ⟨validatorInputs, produced.state.proof, produced.state.oracle⟩ services
            pure ⟨produced, some (Original.mapExecution Prod.snd original)⟩) := by
  have producerLaw := (producerFacts.simulation model producerInputs).runM
    (Domain.handler .producer oracle services) ⟨producerInputs, [], state⟩
  have validatorLaw := fun proof final => (validatorFacts.simulation model validatorInputs).runM
    (Domain.handler .validator oracle services) ⟨validatorInputs, proof, final⟩
  unfold Domain.executePair Domain.produce Domain.validate Domain.run
  erw [producerLaw]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext original
  cases outcome : (Original.mapExecution Prod.snd original).outcome with
  | stopped => rfl
  | returned =>
    erw [validatorLaw]
    simp only [bind_assoc, pure_bind]

/-- Validation also preserves an arbitrary supplied unread proof suffix. -/
theorem validate (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (proof : Domain.Proof model.toCarriers) (oracle : Domain.Oracle m model.toCarriers S)
    (state : S) (services : Domain.LocalServices m model.toCarriers S) :
    Domain.validate model program context validatorArtifact physical proof oracle state services =
      (do let execution ← Domain.run .validator oracle
            (validatorFacts.simulation model physical).paired ⟨physical, proof, state⟩ services
          pure (Original.mapExecution Prod.snd execution)) :=
  (validatorFacts.simulation model physical).runM
    (Domain.handler .validator oracle services) ⟨physical, proof, state⟩

#print axioms execute_pair
#print axioms validate
end Two

end TestsSecurity.OriginalPairExecution
