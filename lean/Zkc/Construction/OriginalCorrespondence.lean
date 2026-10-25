module

public import Zkc.Construction.OriginalInputs
public import Zkc.Construction.OriginalExecution
public import Zkc.Construction.OriginalEffects
public import Zkc.Construction.OriginalInvariant
public import Zkc.Construction.OriginalDerivation

@[expose] public section

/-! The source-indexed assembly boundary. Producer and validator certificates
are separate and fix their exact original, full ABI and selected artifact.
The consumers use the existing nominal evaluator and pair experiment.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source

variable {model : Structured.DomainModel} {program : Structured.Program}

abbrev SourceResult (model : Structured.DomainModel) (program : Structured.Program) :=
  Values (Component model.Value) program.payload.entry.outputs × State model.toCarriers

/-- A producer certificate is anchored at its actual original role. Neither a
free artifact view nor checkProducer can provide this proof. -/
abbrev Producer (routing : Routing) (artifact : Participant)
    (inputs : Domain.Environment model.toCarriers)
    (originalInputs : Values (Component model.Value) program.payload.entry.inputs)
    (initial : State model.toCarriers)
    (related : SourceResult model program → Domain.Result model.toCarriers → Prop)
    (live : PIR.Process (Domain.effects model.toCarriers) (SourceResult model program) →
      Domain.Environment model.toCarriers → Prop) :=
  Simulation related live
    (participant model program { routing with mode := .producer } routing.context.producer originalInputs initial)
    (Domain.participant model program routing.context artifact inputs)

/-- Validator correspondence does not imply producer correspondence. -/
abbrev Validator (routing : Routing) (artifact : Participant)
    (inputs : Domain.Environment model.toCarriers)
    (originalInputs : Values (Component model.Value) program.payload.entry.inputs)
    (initial : State model.toCarriers)
    (related : SourceResult model program → Domain.Result model.toCarriers → Prop)
    (live : PIR.Process (Domain.effects model.toCarriers) (SourceResult model program) →
      Domain.Environment model.toCarriers → Prop) :=
  Simulation related live
    (participant model program { routing with mode := .validator } routing.context.validator originalInputs initial)
    (Domain.participant model program routing.context artifact inputs)

/-- Every actual producer execution is the target projection of the certified
original construction, in the same complete runtime state. -/
theorem produce_eq {routing : Routing} {artifact : Participant}
    {inputs : Domain.Environment model.toCarriers}
    {originalInputs : Values (Component model.Value) program.payload.entry.inputs}
    {initial : State model.toCarriers}
    {related : SourceResult model program → Domain.Result model.toCarriers → Prop}
    {live : PIR.Process (Domain.effects model.toCarriers) (SourceResult model program) →
      Domain.Environment model.toCarriers → Prop}
    (derivation : Producer routing artifact inputs originalInputs initial related live)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S := Domain.refuseLocal) :
    Domain.produce model program routing.context artifact inputs oracle state services =
      (do let execution ← Domain.run .producer oracle derivation.paired ⟨inputs, [], state⟩ services
          pure (mapExecution Prod.snd execution)) :=
  derivation.runM (Domain.handler .producer oracle services) ⟨inputs, [], state⟩

/-- Validation retains the unread proof suffix, failures, exact events, all
ABI results and oracle/private-service post-state. -/
theorem validate_eq {routing : Routing} {artifact : Participant}
    {inputs : Domain.Environment model.toCarriers}
    {originalInputs : Values (Component model.Value) program.payload.entry.inputs}
    {initial : State model.toCarriers}
    {related : SourceResult model program → Domain.Result model.toCarriers → Prop}
    {live : PIR.Process (Domain.effects model.toCarriers) (SourceResult model program) →
      Domain.Environment model.toCarriers → Prop}
    (derivation : Validator routing artifact inputs originalInputs initial related live)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (proof : Domain.Proof model.toCarriers) (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S := Domain.refuseLocal) :
    Domain.validate model program routing.context artifact inputs proof oracle state services =
      (do let execution ← Domain.run .validator oracle derivation.paired ⟨inputs, proof, state⟩ services
          pure (mapExecution Prod.snd execution)) :=
  derivation.runM (Domain.handler .validator oracle services) ⟨inputs, proof, state⟩

/-- The existing pair experiment threads the certified producer's actual proof
and oracle/service post-state into the independently certified validator. A
stopped producer still skips validation. No second pair experiment is defined. -/
theorem executePair_eq {routing : Routing} {producer validator : Participant}
    {producerInputs validatorInputs : Domain.Environment model.toCarriers}
    {originalProducerInputs originalValidatorInputs : Values (Component model.Value) program.payload.entry.inputs}
    {producerInitial validatorInitial : State model.toCarriers}
    {producerRelated validatorRelated : SourceResult model program → Domain.Result model.toCarriers → Prop}
    {producerLive validatorLive : PIR.Process (Domain.effects model.toCarriers) (SourceResult model program) →
      Domain.Environment model.toCarriers → Prop}
    (producerLaw : Producer routing producer producerInputs originalProducerInputs producerInitial producerRelated producerLive)
    (validatorLaw : Validator routing validator validatorInputs originalValidatorInputs validatorInitial validatorRelated validatorLive)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m model.toCarriers S) (state : S)
    (services : Domain.LocalServices m model.toCarriers S := Domain.refuseLocal) :
    Domain.executePair model program routing.context producer validator producerInputs validatorInputs oracle state services =
      (do
        let original ← Domain.run .producer oracle producerLaw.paired ⟨producerInputs, [], state⟩ services
        let produced := mapExecution Prod.snd original
        match produced.outcome with
        | .stopped _ => pure ⟨produced, none⟩
        | .returned _ =>
            let original ← Domain.run .validator oracle validatorLaw.paired
              ⟨validatorInputs, produced.state.proof, produced.state.oracle⟩ services
            pure ⟨produced, some (mapExecution Prod.snd original)⟩) := by
  unfold Domain.executePair
  rw [produce_eq producerLaw oracle state services]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext original
  cases outcome : (mapExecution Prod.snd original).outcome with
  | stopped => rfl
  | returned =>
    rw [validate_eq validatorLaw _ oracle _ services]
    simp only [bind_assoc, pure_bind]

end Zkc.Construction.Original
