module

public import Zkc.Construction.DomainProducer

@[expose] public section

/-! Monadic transport of the shared pair interpreter. These equations preserve
stops, final frames, proof buffers and observations, including state threaded
between participants. They add no probabilistic or cryptographic assumption. -/

set_option autoImplicit false
namespace Zkc.Construction.Domain
open Zkc.Source
variable {m n : Type → Type} [Monad m] [Monad n]
  [MonadLiftT m n] [LawfulMonadLiftT m n] {carriers : Structured.Carriers} {S : Type}

theorem handler_lift (oracle : Oracle m carriers S) (services : LocalServices m carriers S)
    (mode : Mode) (operation : Effect carriers) (state : RuntimeState carriers S) :
    (liftM (handler mode oracle services operation state) : n _) =
      handler mode (fun history event state => liftM (oracle history event state))
        (fun mode port origin state => liftM (services mode port origin state)) operation state := by
  cases operation with
  | checkpoint | observe => simp only [handler, monadLift_pure]
  | send => cases mode <;> simp only [handler, monadLift_pure]
  | receive ty site schema peer =>
      cases mode with
      | producer => simp only [handler, monadLift_pure]
      | validator =>
          cases proof : state.proof with
          | nil => simp only [handler, proof, monadLift_pure]
          | cons payload unread =>
              simp only [handler, proof]
              split <;> simp only [monadLift_pure]
  | localService => simp only [handler, monadLift_bind, monadLift_pure]
  | query =>
      simp only [handler]
      split <;> simp only [monadLift_bind, monadLift_pure]

theorem executePair_lift (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Environment model.toCarriers)
    (oracle : Oracle m model.toCarriers S) (initial : S)
    (services : LocalServices m model.toCarriers S) :
    (liftM (executePair model program context producer validator producerInputs validatorInputs
      oracle initial services) : n _) =
      executePair model program context producer validator producerInputs validatorInputs
        (fun history event state => liftM (oracle history event state)) initial
        (fun mode port origin state => liftM (services mode port origin state)) := by
  have handlers (mode : Mode) :
      (fun operation state => (liftM (handler mode oracle services operation state) : n _)) =
      handler mode (fun history event state => liftM (oracle history event state))
        (fun mode port origin state => liftM (services mode port origin state)) :=
    funext fun operation => funext fun state => handler_lift oracle services mode operation state
  have produceLaw : (liftM (produce model program context producer producerInputs oracle initial services) : n _) =
      produce model program context producer producerInputs
        (fun history event state => liftM (oracle history event state)) initial
        (fun mode port origin state => liftM (services mode port origin state)) := by
    simp only [produce, run, PIR.runM_lift, handlers]
  have validateLaw (proof : Proof model.toCarriers) (state : S) :
      (liftM (validate model program context validator validatorInputs proof oracle state services) : n _) =
      validate model program context validator validatorInputs proof
        (fun history event state => liftM (oracle history event state)) state
        (fun mode port origin state => liftM (services mode port origin state)) := by
    simp only [validate, run, PIR.runM_lift, handlers]
  simp only [executePair, monadLift_bind, produceLaw]
  congr 1
  funext produced
  cases produced.outcome <;> simp only [monadLift_pure, monadLift_bind, validateLaw]

end Zkc.Construction.Domain
