import Zkc.Protocols.CorrelatedSetup.Execution
import Zkc.Compiler.Transformation

/-! Shared immutable coefficient caching with persistent response randomness.

Only `byPrefix` is cached. Every actual request still consumes a distinct tape
entry, including partially delivered responses. The relation preserves the
whole visible history, remaining tape, terminal outcome and emitted events;
cached coefficients are private representation state.
-/

set_option autoImplicit false

namespace Zkc.Protocols.CorrelatedSetup.Preparation

open PIR Zkc.Modules Zkc.Source Zkc.Compiler Service

variable {F : Type} [CommRing F] [DecidableEq F]

structure State (F : Type) where
  history : History F
  tape : List F
  coefficients : ImmutableCache.Cache (Triple F) (F × F)

def initial (history : History F) (tape : List F) : State F :=
  ⟨history, tape, ImmutableCache.empty⟩

def Rel (setup : Setup F) (witness : Witness F)
    (reference : History F × List F) (cached : State F) : Prop :=
  reference.1 = cached.history ∧ reference.2 = cached.tape ∧
    ImmutableCache.Valid (byPrefix setup witness) cached.coefficients

def handler (setup : Setup F) (witness : Witness F) (publication : Triple F) :
    Handler (Execution.sig F) (State F) (Event F)
  | .stop, state =>
      ⟨.returned (), { state with history := ⟨state.history.events ++ [.stopped], true⟩ }, [.stopped]⟩
  | .request _, ⟨history, [], cache⟩ => ⟨.stopped .exhausted, ⟨history, [], cache⟩, []⟩
  | .request request, ⟨history, coin :: tape, cache⟩ =>
      let prepared := ImmutableCache.lookup (byPrefix setup witness) (fun _ _ => true) cache publication
      let reply := Execution.deliver request.cutAfterU
        (actualResponse setup prepared.1 request coin) (tags setup (publicationsOf witness publication)).2.2
      ⟨.returned reply, ⟨Execution.receive history request reply, tape, prepared.2⟩,
        [Execution.event request reply]⟩

theorem handlers_related (setup : Setup F) (witness : Witness F) (publication : Triple F) :
    HandlerRelated (Rel setup witness) (fun event => [event]) (fun event => [event])
      (Execution.handler setup witness publication) (handler setup witness publication) := by
  intro op reference cached relation
  rcases reference with ⟨history, tape⟩
  rcases cached with ⟨otherHistory, otherTape, cache⟩
  rcases relation with ⟨sameHistory, sameTape, valid⟩
  dsimp only at sameHistory sameTape valid
  subst otherHistory
  subst otherTape
  cases op with
  | stop => exact ⟨rfl, ⟨rfl, rfl, valid⟩, rfl⟩
  | request request =>
      cases tape with
      | nil => exact ⟨rfl, ⟨rfl, rfl, valid⟩, rfl⟩
      | cons coin tape =>
          have value := ImmutableCache.lookup_value (byPrefix setup witness)
            (fun _ _ => true) cache publication valid
          have nextValid := ImmutableCache.lookup_valid (byPrefix setup witness)
            (fun _ _ => true) cache publication valid
          simp only [handler, Execution.handler]
          rw [value]
          exact ⟨rfl, ⟨rfl, rfl, nextValid⟩, rfl⟩

theorem run_refines (setup : Setup F) (witness : Witness F) (publication : Triple F)
    {A : Type} (program : Proc (Execution.sig F) A)
    (reference : History F × List F) (cached : State F) (valid : Rel setup witness reference cached) :
    Related (Rel setup witness) (fun event => [event]) (fun event => [event])
      (program.run (Execution.handler setup witness publication) reference)
      (program.run (handler setup witness publication) cached) :=
  run_related _ _ _ _ _ (handlers_related setup witness publication) program reference cached valid

abbrev sourceModel {language : Language} (meaning : Interpretation language (Execution.sig F))
    (setup : Setup F) (witness : Witness F) (publication : Triple F) : ExecutionModel language where
  interface := Execution.sig F
  meaning := meaning
  State := History F × List F
  Event := Event F
  handler := Execution.handler setup witness publication

abbrev targetModel {language : Language} (meaning : Interpretation language (Execution.sig F))
    (setup : Setup F) (witness : Witness F) (publication : Triple F) : ExecutionModel language where
  interface := Execution.sig F
  meaning := meaning
  State := State F
  Event := Event F
  handler := handler setup witness publication

def refinement {language : Language} (meaning : Interpretation language (Execution.sig F))
    (setup : Setup F) (witness : Witness F) (publication : Triple F)
    (Γ : List language.Ty) (ty : language.Ty) :
    Refinement (sourceModel meaning setup witness publication)
      (targetModel meaning setup witness publication) Γ Γ ty ty where
  initial left reference right cached :=
    @Eq (Environment meaning.Value Γ) left right ∧ Rel setup witness reference cached
  states := Rel setup witness
  values left _ right _ := left = right
  Observation := Event F
  sourceView event := [event]
  targetView event := [event]

/-- The same source/candidate checker admits a different handler realization.
This is an implementation-selection rule; its typed control syntax stays fixed. -/
def rule {language : Language} (meaning : Interpretation language (Execution.sig F))
    (setup : Setup F) (witness : Witness F) (publication : Triple F)
    (Γ : List language.Ty) (ty : language.Ty) :
    TransformationRule (refinement meaning setup witness publication Γ ty) where
  Certificate := Unit
  apply source _ := some (lower source)
  sound source _ plan accepted := by
    cases Option.some.inj accepted
    intro left reference right cached admitted
    have inputs := admitted.1
    have state := admitted.2
    have same : (source.denote meaning left).run (Execution.handler setup witness publication) reference =
        (source.denote meaning right).run (Execution.handler setup witness publication) reference :=
      congrArg (fun env : Environment meaning.Value Γ =>
        (source.denote meaning env).run (Execution.handler setup witness publication) reference) inputs
    apply PIR.Execution.Relates.of_related
    change Related (Rel setup witness) (fun event => [event]) (fun event => [event])
      ((source.denote meaning left).run (Execution.handler setup witness publication) reference)
      ((lower source).run meaning (handler setup witness publication) right cached)
    rw [same, lower_correct]
    exact run_refines setup witness publication _ reference cached state

theorem source_history (setup : Setup F) (witness : Witness F) (controller : Controller F)
    (publication : Triple F) (count : Nat) (history : History F)
    (tape : Zkc.Probability.AdaptiveTape.Tape F count) :
    ((Execution.source controller publication count history).run
      (handler setup witness publication) (initial history (Execution.tapeList count tape))).outcome =
      .returned (Zkc.Probability.AdaptiveTape.run (realStep setup witness controller publication)
        count history tape) := by
  have related := run_refines setup witness publication
    (Execution.source controller publication count history)
    (history, Execution.tapeList count tape) (initial history (Execution.tapeList count tape))
    ⟨rfl, rfl, ImmutableCache.empty_valid _⟩
  rw [← related.outcome]
  exact Execution.history_exact setup witness controller publication count history tape

/-- The declared observation includes the joint publication and terminal
history outcome. It excludes private coefficient storage and unused coins. -/
def experiment (setup : Setup F) (witness : Witness F) (controller : Controller F)
    (count : Nat) (coins : Triple F × Zkc.Probability.AdaptiveTape.Tape F count) :=
  let publication := publicationsOf witness coins.1
  (publication, ((Execution.source controller publication count empty).run
    (handler setup witness publication) (initial empty (Execution.tapeList count coins.2))).outcome)

theorem experiment_coupling (setup : Setup F) (witness : Witness F) (controller : Controller F)
    (count : Nat) (coins : Triple F × Zkc.Probability.AdaptiveTape.Tape F count) :
    experiment setup witness controller count coins =
      let output := simulated setup controller count (wholeCoins setup witness controller count coins)
      (output.1, Outcome.returned output.2) := by
  simp only [experiment, source_history]
  exact congrArg (fun output : Triple F × History F => (output.1, Outcome.returned output.2))
    (whole_coupling setup witness controller count coins)

/-- Exact uniform finite-mass transport for the same admitted controller.
An arbitrary witness-dependent host closure does not satisfy that scope. -/
theorem experiment_mass [Fintype F]
    (setup : Setup F) (witness : Witness F) (controller : Controller F)
    (count : Nat) (output : Triple F × Outcome (History F)) :
    (Fintype.card {coins : Triple F × Zkc.Probability.AdaptiveTape.Tape F count //
      experiment setup witness controller count coins = output} : ℚ) /
        Fintype.card (Triple F × Zkc.Probability.AdaptiveTape.Tape F count) =
    (Fintype.card {coins : Triple F × Zkc.Probability.AdaptiveTape.Tape F count //
      (let result := simulated setup controller count coins
       (result.1, Outcome.returned result.2)) = output} : ℚ) /
        Fintype.card (Triple F × Zkc.Probability.AdaptiveTape.Tape F count) := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv
    (wholeCoins setup witness controller count) (experiment setup witness controller count)
    (fun coins => let result := simulated setup controller count coins
      (result.1, Outcome.returned result.2))
    (experiment_coupling setup witness controller count) output)]

end Zkc.Protocols.CorrelatedSetup.Preparation
