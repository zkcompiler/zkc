module

public import Zkc.Realization.QuerySourceContinuation
public import Zkc.Source.Structured.OracleProcessContinuation

@[expose] public section

/-! A source cursor with its actual open-execution prefix. `Associated` alone
records typed replies; it does not establish their production. This relation
adds reachability through the existing source presentation, retaining provider
state, interaction phase and event order. It introduces no body evaluator.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Realization.QuerySourceContinuation
open Zkc.Source Zkc.Source.Structured
variable {model : DomainModel} {I : PIR.Signature} {S E A : Type}

/-- A derivation of actual source-query progress, not a second evaluator.
Each resumption records the execution that produced its saved value. Keeping
the derivation is essential when the source ignores an earlier answer: the
final execution result alone cannot recover that answer's provenance. -/
inductive Produced (interaction : PIR.Interaction I)
    (operations : (request : OracleRead) → S →
      PIR.Process I (PIR.Execution S E (model.Value request.kind.answer)))
    (source : PIR.Process (oracleReadInterface model.toCarriers) A)
    (initialState : S) (initialPhase : interaction.Phase) :
    ((kind : OracleKind) → List (model.Value kind.answer)) →
    PIR.Process (oracleReadInterface model.toCarriers) A → List Nat →
    S → interaction.Phase → List E → Type where
  | initial (arenas) : Produced interaction operations source initialState initialPhase
      arenas source [] initialState initialPhase []
  | transport {before after residual indices state phase events}
      (produced : Produced interaction operations source initialState initialPhase
        before residual indices state phase events)
      (extension : ∀ kind, before kind <+: after kind) :
      Produced interaction operations source initialState initialPhase
        after residual indices state phase events
  | resume {arenas request next indices state phase events slot reply after final following}
      (produced : Produced interaction operations source initialState initialPhase arenas
        (.call request next) indices state phase events)
      (child : PIR.Reaches interaction (operations request state) phase
        (.done ⟨.returned reply, after, following⟩) final)
      (stored : (arenas request.kind)[slot]? = some reply) :
      Produced interaction operations source initialState initialPhase arenas
        (next reply) (indices ++ [slot]) after final (events ++ following)

variable {interaction : PIR.Interaction I}
  {operations : (request : OracleRead) → S →
    PIR.Process I (PIR.Execution S E (model.Value request.kind.answer))}
  {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
  {initialState currentState : S} {initialPhase currentPhase : interaction.Phase}
  {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
  {indices : List Nat} {events : List E}

/-- Recover the typed source cursor from the actual progress derivation.
The cursor and execution evidence cannot be chosen independently. -/
noncomputable def Produced.cursor
    (produced : Produced interaction operations source initialState initialPhase arenas
      residual indices currentState currentPhase events) :
    Associated arenas source residual indices := by
  induction produced with
  | initial arenas => exact QuerySourceContinuation.initial arenas source
  | transport before extension ih => exact ih.transport extension
  | resume before child stored ih => exact ih.resume stored

/-- Every derivation is a path in the existing open presentation, with the
same provider state, phase and ordered event prefix. -/
theorem Produced.executed
    (produced : Produced interaction operations source initialState initialPhase arenas
      residual indices currentState currentPhase events) :
    PIR.Reaches interaction (OracleProcess.present operations source initialState) initialPhase
      (OracleProcess.prependEvents events (OracleProcess.present operations residual currentState))
      currentPhase := by
  induction produced with
  | initial arenas => rw [OracleProcess.prependEvents_nil]; exact .refl _ _
  | transport before extension ih => exact ih
  | @resume arenas request next indices state phase events slot reply after final following
      before child stored ih =>
      have reached := OracleProcess.prependEvents_reaches
        (OracleProcess.present_returned (I := oracleReadInterface model.toCarriers)
          operations request next child) events
      rw [OracleProcess.prependEvents_append] at reached
      exact ih.trans reached

/-- An empty saved prefix cannot have advanced source or provider state.
Arena growth is administrative and cannot fabricate an execution step. -/
theorem Produced.zero
    (produced : Produced interaction operations source initialState initialPhase arenas
      residual indices currentState currentPhase events) (empty : indices = []) :
    residual = source ∧ currentState = initialState ∧
      currentPhase = initialPhase ∧ events = [] := by
  induction produced with
  | initial _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | transport before extension ih => exact ih empty
  | resume before child stored ih => simp at empty

/-- A single saved answer determines the actual first child execution, not
only its eventual contribution to the parent's final result. -/
theorem Produced.one
    (produced : Produced interaction operations source initialState initialPhase arenas
      residual indices currentState currentPhase events)
    {slot : Nat} (one : indices = [slot]) :
    ∃ (request : OracleRead)
      (next : model.Value request.kind.answer →
        PIR.Process (oracleReadInterface model.toCarriers) A)
      (reply : model.Value request.kind.answer),
      source = .call request next ∧ residual = next reply ∧
      PIR.Reaches interaction (operations request initialState) initialPhase
        (.done ⟨.returned reply, currentState, events⟩) currentPhase ∧
      (arenas request.kind)[slot]? = some reply := by
  induction produced with
  | initial => simp at one
  | transport before extension ih =>
      obtain ⟨request, next, reply, sourceEq, residualEq, executed, stored⟩ := ih one
      refine ⟨request, next, reply, sourceEq, residualEq, executed, ?_⟩
      obtain ⟨suffix, changed⟩ := extension request.kind
      rw [← changed]
      exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1).trans stored
  | @resume arenas request next indices state phase events cell reply after final following
      before child stored ih =>
      have empty : indices = [] := by
        have lengths := congrArg List.length one
        simp only [List.length_append, List.length_cons, List.length_nil] at lengths
        cases indices with
        | nil => rfl
        | cons => simp only [List.length_cons] at lengths; omega
      obtain ⟨sourceEq, stateEq, phaseEq, eventsEq⟩ := before.zero empty
      have cellEq : cell = slot := by simpa only [empty, List.nil_append, List.cons.injEq,
        and_true] using one
      refine ⟨request, next, reply, sourceEq.symm, rfl, ?_, ?_⟩
      · simpa only [stateEq, phaseEq, eventsEq, List.nil_append] using child
      · simpa only [cellEq] using stored

/-- Failed child execution closes the source path with the real stopped
poststate and the complete prefix, without producing a cursor advance. -/
theorem Produced.stopped {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers) A}
    (produced : Produced interaction operations source initialState initialPhase arenas
      (.call request next) indices currentState currentPhase events)
    {after : S} {phase : interaction.Phase} {following : List E} {reason : PIR.Stop}
    (child : PIR.Reaches interaction (operations request currentState) currentPhase
      (.done ⟨.stopped reason, after, following⟩) phase) :
    PIR.Reaches interaction (OracleProcess.present operations source initialState) initialPhase
      (.done ⟨.stopped reason, after, events ++ following⟩) phase :=
  produced.executed.trans
    (OracleProcess.prependEvents_reaches
      (OracleProcess.present_stopped (I := oracleReadInterface model.toCarriers)
        operations request next child) events)

theorem Produced.completed {value : A}
    (produced : Produced interaction operations source initialState initialPhase arenas
      (.done value) indices currentState currentPhase events) :
    PIR.Reaches interaction (OracleProcess.present operations source initialState) initialPhase
      (.done ⟨.returned value, currentState, events⟩) currentPhase := by
  simpa only [OracleProcess.prependEvents, OracleProcess.mapResult, OracleProcess.present,
    PIR.Process.bind, List.append_nil] using produced.executed

end Zkc.Realization.QuerySourceContinuation
