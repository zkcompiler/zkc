module

public import ZkcSecurity.FiatShamir.HonestSampling
public import Zkc.Construction.DomainProducer

@[expose] public section

/-! Oracle simulation commutes with the actual sequential pair interpreter.
Fixing public answers may leave a probabilistic private-service computation.
These laws preserve stops, full results, environments, observations and state.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.HonestSampling
open Zkc.Source Zkc.Construction OracleComp OracleSpec

variable {K : Type} {spec : OracleSpec K} {m : Type → Type}
  [Monad m] [LawfulMonad m] {I : PIR.Signature} {S E A B : Type}

/-- Fixing a public table evaluates only the transcript summand. This law is
useful for the model's lifted public oracle; it says nothing about uniforms. -/
theorem simulate_transcript (answers : QueryImpl spec Id) (computation : OracleComp spec A) :
    simulateQ (unifFwdAnswerImpl answers)
      (liftM computation : OracleComp (unifSpec + spec) A) =
      pure (evalWithAnswerFn answers computation) := by
  calc
    _ = simulateQ (answers.liftTarget ProbComp) computation :=
      QueryImpl.simulateQ_add_liftM_right _ _ _
    _ = _ := by rw [simulateQ_liftTarget]; rfl

theorem simulate_followM (impl : QueryImpl spec m) (execution : PIR.Execution S E A)
    (next : A → S → OracleComp spec (PIR.Execution S E B)) :
    simulateQ impl (execution.followM next) =
      execution.followM (fun value state => simulateQ impl (next value state)) := by
  rcases execution with ⟨outcome, state, events⟩
  cases outcome <;> simp only [PIR.Execution.followM, simulateQ_bind, simulateQ_pure]

theorem simulate_runM (impl : QueryImpl spec m)
    (handler : PIR.MonadHandler (OracleComp spec) I S E)
    (process : PIR.Process I A) (state : S) :
    simulateQ impl (process.runM handler state) =
      process.runM (fun operation state => simulateQ impl (handler operation state)) state := by
  induction process generalizing state with
  | done value => exact simulateQ_pure _ _
  | halt reason => exact simulateQ_pure _ _
  | call operation next ih =>
      simp only [PIR.Process.runM, simulateQ_bind, simulate_followM]
      congr 1
      funext execution
      congr 1
      funext value state
      exact ih value state

variable {carriers : Structured.Carriers}

theorem simulate_handler (impl : QueryImpl spec m)
    (oracle : Domain.Oracle (OracleComp spec) carriers S)
    (services : Domain.LocalServices (OracleComp spec) carriers S)
    (mode : Domain.Mode) (operation : Domain.Effect carriers)
    (state : Domain.RuntimeState carriers S) :
    simulateQ impl (Domain.handler mode oracle services operation state) =
      Domain.handler mode (fun history event state => simulateQ impl (oracle history event state))
        (fun mode port origin state => simulateQ impl (services mode port origin state))
        operation state := by
  cases operation with
  | checkpoint | observe => exact simulateQ_pure _ _
  | send => cases mode <;> exact simulateQ_pure _ _
  | receive ty site schema peer =>
      cases mode with
      | producer => exact simulateQ_pure _ _
      | validator =>
          cases proof : state.proof with
          | nil => simp only [Domain.handler, proof, simulateQ_pure]
          | cons payload unread =>
              simp only [Domain.handler, proof]
              split <;> exact simulateQ_pure _ _
  | localService port origin => simp only [Domain.handler, simulateQ_bind, simulateQ_pure]
  | query history origin =>
      simp only [Domain.handler]
      split <;> simp only [simulateQ_bind, simulateQ_pure]

/-- No phase reset: simulation passes the producer's actual proof and state to
the actual validator, and never runs validation after a producer stop. -/
theorem simulate_executePair (impl : QueryImpl spec m)
    (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (oracle : Domain.Oracle (OracleComp spec) model.toCarriers S)
    (initial : S) (services : Domain.LocalServices (OracleComp spec) model.toCarriers S) :
    simulateQ impl (Domain.executePair model program context producer validator
      producerInputs validatorInputs oracle initial services) =
      Domain.executePair model program context producer validator producerInputs validatorInputs
        (fun history event state => simulateQ impl (oracle history event state)) initial
        (fun mode port origin state => simulateQ impl (services mode port origin state)) := by
  have handlerEquality (mode : Domain.Mode) :
      (fun operation state => simulateQ impl (Domain.handler mode oracle services operation state)) =
      Domain.handler mode (fun history event state => simulateQ impl (oracle history event state))
        (fun mode port origin state => simulateQ impl (services mode port origin state)) :=
    funext fun operation => funext fun state => simulate_handler impl oracle services mode operation state
  have producerLaw : simulateQ impl
      (Domain.produce model program context producer producerInputs oracle initial services) =
      Domain.produce model program context producer producerInputs
        (fun history event state => simulateQ impl (oracle history event state)) initial
        (fun mode port origin state => simulateQ impl (services mode port origin state)) := by
    simp only [Domain.produce, Domain.run, simulate_runM, handlerEquality]
  have validatorLaw (proof : Domain.Proof model.toCarriers) (state : S) : simulateQ impl
      (Domain.validate model program context validator validatorInputs proof oracle state services) =
      Domain.validate model program context validator validatorInputs proof
        (fun history event state => simulateQ impl (oracle history event state)) state
        (fun mode port origin state => simulateQ impl (services mode port origin state)) := by
    simp only [Domain.validate, Domain.run, simulate_runM, handlerEquality]
  simp only [Domain.executePair, simulateQ_bind, producerLaw]
  congr 1
  funext produced
  cases produced.outcome <;> simp only [simulateQ_pure, simulateQ_bind, validatorLaw]

end ZkcSecurity.FiatShamir.HonestSampling
