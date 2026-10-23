module

public import Zkc.Construction.DomainProducer
public import ZkcSecurity.FiatShamir.Honest

@[expose] public section

/-! Actual compiled producer followed by actual compiled verifier. Artifact
admission and source input selection are supplied by the typed claim subject. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.HonestCompiled
open Zkc.Source Zkc.Construction
open OracleComp OracleSpec

abbrev Spec (carriers : Structured.Carriers) := Honest.Spec (@Domain.Raw carriers)

/-- Domain's explicit oracle-state parameter is Unit because the coherent
cache belongs to the outer StateT simulation, not to either participant. -/
def oracle {carriers : Structured.Carriers} : Domain.Oracle (OracleComp (Spec carriers)) carriers Unit :=
  fun history event state => do
    let answer ← Typed.ask (R := Typed.ByLast Domain.Raw) history event
    pure (.returned answer, state)

/-- Fixed-table evaluation commutes with the full execution interpreter,
including stops, post-state and ordered observations. -/
theorem eval_followM {I S E A B : Type} {spec : OracleSpec I}
    (answers : QueryImpl spec Id) (execution : PIR.Execution S E A)
    (next : A → S → OracleComp spec (PIR.Execution S E B)) :
    evalWithAnswerFn answers (execution.followM next) =
      execution.followM (m := Id) (fun value state => evalWithAnswerFn answers (next value state)) := by
  rcases execution with ⟨outcome, state, events⟩
  cases outcome <;> simp only [PIR.Execution.followM, evalWithAnswerFn_bind, evalWithAnswerFn_pure] <;> rfl

theorem eval_runM {I : PIR.Signature} {S E A K : Type} {spec : OracleSpec K}
    (answers : QueryImpl spec Id)
    (handler : PIR.MonadHandler (OracleComp spec) I S E) (process : PIR.Process I A) (state : S) :
    evalWithAnswerFn answers (process.runM handler state) =
      process.runM (m := Id) (fun operation state => evalWithAnswerFn answers (handler operation state)) state := by
  induction process generalizing state with
  | done value => rfl
  | halt reason => rfl
  | call operation next ih =>
      simp only [PIR.Process.runM, evalWithAnswerFn_bind, eval_followM]
      congr 1
      funext value state
      exact ih value state

def tableOracle {carriers : Structured.Carriers} (answers : QueryImpl (Spec carriers) Id) :
    Domain.Oracle Id carriers Unit := fun history event state =>
  (.returned (Typed.readTable (R := Typed.ByLast Domain.Raw) answers history event), state)

theorem eval_oracle {carriers : Structured.Carriers} (answers : QueryImpl (Spec carriers) Id)
    (history : Domain.History carriers) (event : Domain.Event carriers) (state : Unit) :
    evalWithAnswerFn answers (oracle history event state) = tableOracle answers history event state := by
  simp only [oracle, Typed.ask, Typed.answer, evalWithAnswerFn_bind, evalWithAnswerFn_map,
    evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure, tableOracle, Typed.readTable]

theorem eval_handler {carriers : Structured.Carriers} (answers : QueryImpl (Spec carriers) Id)
    (mode : Domain.Mode) (operation : Domain.Effect carriers) (state : Domain.RuntimeState carriers Unit) :
    evalWithAnswerFn answers (Domain.handler mode oracle operation state) =
      Domain.handler mode (tableOracle answers) operation state := by
  cases operation with
  | checkpoint | observe => rfl
  | send => cases mode <;> rfl
  | receive ty site schema peer =>
      cases mode with
      | producer => rfl
      | validator =>
          rcases state with ⟨environment, proof, state⟩
          cases proof with
          | nil => rfl
          | cons payload unread =>
              simp only [Domain.handler]
              split <;> rfl
  | query history origin =>
      simp only [Domain.handler]
      split
      · rfl
      · rfl

def computation (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers) :
    OracleComp (Spec model.toCarriers) (Domain.PairExecution model.toCarriers Unit) :=
  Domain.executePair model program context producer validator producerInputs validatorInputs oracle ()

theorem eval_computation (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (answers : QueryImpl (Spec model.toCarriers) Id) :
    evalWithAnswerFn answers (computation model program context producer validator producerInputs validatorInputs) =
      Domain.executePair model program context producer validator producerInputs validatorInputs (tableOracle answers) () := by
  have handlerEquality (mode : Domain.Mode) :
      (fun operation state => evalWithAnswerFn answers (Domain.handler mode oracle operation state)) =
        Domain.handler mode (tableOracle answers) :=
    funext fun operation => funext fun state => eval_handler answers mode operation state
  have producerLaw : evalWithAnswerFn answers
      (Domain.produce model program context producer producerInputs oracle ()) =
      Domain.produce model program context producer producerInputs (tableOracle answers) () := by
    simp only [Domain.produce, Domain.run, eval_runM]
    rw [handlerEquality .producer]
  have validatorLaw (proof : Domain.Proof model.toCarriers) (state : Unit) :
      evalWithAnswerFn answers
        (Domain.validate model program context validator validatorInputs proof oracle state) =
      Domain.validate model program context validator validatorInputs proof (tableOracle answers) state := by
    simp only [Domain.validate, Domain.run, eval_runM]
    rw [handlerEquality .validator]
  simp only [computation, Domain.executePair, evalWithAnswerFn_bind, producerLaw]
  generalize Domain.produce model program context producer producerInputs (tableOracle answers) () = produced
  dsimp only [bind, pure, Id.instMonad]
  cases outcome : produced.outcome
  case returned =>
    change evalWithAnswerFn answers
      ((Domain.validate model program context validator validatorInputs produced.state.proof oracle
        produced.state.oracle) >>= fun validated => pure (Domain.PairExecution.mk produced (some validated))) = _
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_pure, validatorLaw]
  case stopped =>
    rfl

def acceptanceAt {carriers : Structured.Carriers} (position : Nat)
    (values : Domain.Environment carriers) : Option Bool :=
  match values[position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- Every phase must return, the exact generated proof must be exhausted, and
the selected Boolean return must be true. Stops cannot satisfy this event. -/
def Success {carriers : Structured.Carriers} (position : Nat)
    (observed : Domain.PairExecution carriers Unit) : Prop :=
  ∃ produced validated result,
    observed.producer.outcome = .returned produced ∧
    observed.validator = some validated ∧ validated.outcome = .returned result ∧
    validated.state.proof = [] ∧ acceptanceAt position result.values = some true

theorem stopped_fails {carriers : Structured.Carriers} (position : Nat)
    (observed : Domain.PairExecution carriers Unit) (reason : PIR.Stop)
    (stopped : observed.producer.outcome = .stopped reason) : ¬ Success position observed := by
  rintro ⟨_, _, _, returned, _⟩
  rw [stopped] at returned
  cases returned

theorem unread_fails {carriers : Structured.Carriers} (position : Nat)
    (observed : Domain.PairExecution carriers Unit)
    (validated : PIR.Execution (Domain.RuntimeState carriers Unit) (Domain.Event carriers)
      (Domain.Result carriers))
    (selected : observed.validator = some validated) (unread : validated.state.proof ≠ []) :
    ¬ Success position observed := by
  rintro ⟨_, _, _, _, same, _, consumed, _⟩
  rw [selected] at same
  cases Option.some.inj same
  exact unread consumed

theorem false_fails {carriers : Structured.Carriers} (position : Nat)
    (observed : Domain.PairExecution carriers Unit)
    (validated : PIR.Execution (Domain.RuntimeState carriers Unit) (Domain.Event carriers)
      (Domain.Result carriers)) (selected : observed.validator = some validated)
    (result : Domain.Result carriers) (returned : validated.outcome = .returned result)
    (rejected : acceptanceAt position result.values = some false) : ¬ Success position observed := by
  rintro ⟨_, actual, value, _, same, completed, _, accepted⟩
  rw [selected] at same
  cases Option.some.inj same
  rw [returned] at completed
  cases PIR.Outcome.returned.inj completed
  rw [rejected] at accepted
  cases accepted

end ZkcSecurity.FiatShamir.HonestCompiled
