module

public import Zkc.Construction.PairAcceptance
public import ZkcSecurity.Transformations.FiatShamir.TranscriptOracle
public import ZkcSecurity.ProgramLogic.Honest.Honest
public import Zkc.Semantics.WeakestPrecondition

@[expose] public section

/-! Actual compiled producer followed by actual compiled verifier. Artifact
admission and source input selection are supplied by the typed claim subject. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.HonestCompiled
open Zkc.Source Zkc.Construction
open OracleComp OracleSpec
open Std.WP

/-- Domain's explicit oracle-state parameter is Unit because the coherent
cache belongs to the outer StateT simulation, not to either participant. -/
def oracle {carriers : Structured.Carriers} : Domain.Oracle (OracleComp (TranscriptOracle.DomainSpec carriers)) carriers Unit :=
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

def tableOracle {carriers : Structured.Carriers} (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Domain.Oracle Id carriers Unit := fun history event state =>
  (.returned (Typed.readTable (R := Typed.ByLast Domain.Raw) answers history event), state)

theorem eval_oracle {carriers : Structured.Carriers} (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (history : Domain.History carriers) (event : Domain.Event carriers) (state : Unit) :
    evalWithAnswerFn answers (oracle history event state) = tableOracle answers history event state := by
  simp only [oracle, Typed.ask, Typed.answer, evalWithAnswerFn_bind, evalWithAnswerFn_map,
    evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure, tableOracle, Typed.readTable]

theorem eval_handler {carriers : Structured.Carriers} (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (mode : Domain.Mode) (operation : Domain.Effect carriers) (state : Domain.RuntimeState carriers Unit) :
    evalWithAnswerFn answers (Domain.handler mode oracle Domain.refuseLocal operation state) =
      Domain.handler mode (tableOracle answers) Domain.refuseLocal operation state := by
  cases operation with
  | checkpoint | observe | localService => rfl
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
    OracleComp (TranscriptOracle.DomainSpec model.toCarriers) (Domain.PairExecution model.toCarriers Unit) :=
  Domain.executePair model program context producer validator producerInputs validatorInputs oracle ()

theorem eval_computation (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id) :
    evalWithAnswerFn answers (computation model program context producer validator producerInputs validatorInputs) =
      Domain.executePair model program context producer validator producerInputs validatorInputs (tableOracle answers) () := by
  have handlerEquality (mode : Domain.Mode) :
      (fun operation state => evalWithAnswerFn answers (Domain.handler mode oracle Domain.refuseLocal operation state)) =
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

/-- Pointwise completeness of both actual participants on the same answer
table. Validation receives the producer's actual proof and oracle post-state.
Both phases must return, and the validator must consume the whole proof.
Each phase has its own event list, as in `Domain.PairExecution`. -/
def pairWP (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat)
    (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id) : Prop :=
  letI := PIR.WeakestPrecondition.wpMonad (Domain.handler .producer (tableOracle answers))
  Std.WP.wp (Domain.participant model program context producer producerInputs)
    (fun _ produced _ =>
      letI := PIR.WeakestPrecondition.wpMonad (Domain.handler .validator (tableOracle answers))
      Std.WP.wp (Domain.participant model program context validator validatorInputs)
        (fun result validated _ => validated.proof = [] ∧
          Domain.acceptanceAt position result.values = some true)
        estack⟨fun _ _ _ => False⟩
        ⟨validatorInputs, produced.proof, produced.oracle⟩ [])
    estack⟨fun _ _ _ => False⟩ ⟨producerInputs, [], ()⟩ []

/-- The pointwise WP is precisely the existing whole-pair success event.
No probability law or new acceptance policy is introduced. -/
theorem pair_success_iff_wp (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat)
    (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id) :
    Domain.PairExecution.Success position
      (Domain.executePair (m := Id) model program context producer validator
        producerInputs validatorInputs (tableOracle answers) ()) ↔
      pairWP model program context producer validator producerInputs validatorInputs position answers := by
  have produceLaw := PIR.runM_pure (m := Id)
    (Domain.handler .producer (tableOracle answers))
    (Domain.participant model program context producer producerInputs) ⟨producerInputs, [], ()⟩
  have validateLaw (proof : Domain.Proof model.toCarriers) := PIR.runM_pure (m := Id)
    (Domain.handler .validator (tableOracle answers))
    (Domain.participant model program context validator validatorInputs) ⟨validatorInputs, proof, ()⟩
  change Domain.produce model program context producer producerInputs (tableOracle answers) () = _ at produceLaw
  change ∀ proof, Domain.validate model program context validator validatorInputs proof
    (tableOracle answers) () = _ at validateLaw
  simp only [Domain.executePair, produceLaw]
  unfold pairWP
  simp only [PIR.WeakestPrecondition.wp_eq_run]
  generalize (Domain.participant model program context producer producerInputs).run
    (Domain.handler .producer (tableOracle answers)) ⟨producerInputs, [], ()⟩ = produced
  rcases produced with ⟨outcome, ⟨environment, proof, oracleState⟩, events⟩
  cases oracleState
  cases outcome with
  | stopped reason => simp [Domain.PairExecution.Success, PIR.WeakestPrecondition.satisfies]
  | returned value =>
    simp only [Bind.bind, Pure.pure, validateLaw]
    simp only [PIR.WeakestPrecondition.satisfies]
    generalize (Domain.participant model program context validator validatorInputs).run
      (Domain.handler .validator (tableOracle answers)) ⟨validatorInputs, proof, ()⟩ = validated
    rcases validated with ⟨outcome, state, events⟩
    cases outcome <;> simp [Domain.PairExecution.Success]

end ZkcSecurity.FiatShamir.HonestCompiled
