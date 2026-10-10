import Zkc.Compiler.Analysis.FactorReuse
import Zkc.Source.FactorQueries
import Zkc.Compiler.Transformation
import Zkc.Semantics.StateInvariant

/-! Source-relative factor planning under actual outcome-specific state laws.

Each external result selects its own fact and availability transfer. Equal
transfers share one rewritten continuation; differing transfers can still cause
exponential syntax growth. Loops keep their direct body and discard analysis
facts at their exit. Readiness is checked at the original query position in both
executions, including failed prefixes.
-/

set_option autoImplicit false

namespace Zkc.Compiler.FactorOptimization

open Source Source.FactorQueries FactorReuse Modules.Factor Modules.FactorState

def rewrite (summaries : Nat → Bool → Summary) (facts : List Fact) (available : List Nat)
    {Γ ty} : Program language Γ ty → Program plannedLanguage Γ ty
  | .ret value => .ret value
  | .stop why => .stop why
  | .letOp (.evaluate query) _ next =>
      .letOp (.evaluate query (infer facts available query)) .nil
        (rewrite summaries facts available next)
  | .letOp (.external name) _ next =>
      let successFacts := nextFacts (summaries name true) facts
      let failureFacts := nextFacts (summaries name false) facts
      let successKnown := nextKnown (summaries name true) available
      let failureKnown := nextKnown (summaries name false) available
      if successFacts = failureFacts ∧ successKnown = failureKnown then
        .letOp (.external name) .nil (rewrite summaries successFacts successKnown next)
      else
        .letOp (.external name) .nil (.branch .here
          (rewrite summaries successFacts successKnown next)
          (rewrite summaries failureFacts failureKnown next))
  | .letOp .equal args next => .letOp .equal args (rewrite summaries facts available next)
  | .branch condition yes no => .branch condition
      (rewrite summaries facts available yes) (rewrite summaries facts available no)
  | .iterate count initial body next =>
      .iterate count initial (direct body) (rewrite summaries [] [] next)

variable {F E : Type} [DecidableEq F]

abbrev handler (implement : Nat → Implementation F E) :=
  Zkc.Modules.FactorExecution.guard World.known (Zkc.Modules.FactorExecution.handler implement)

/-- This rule consumes contracts valid at every call state. More selective
preconditions need a separate proved applicability analysis. -/
structure Laws (invariant : World F → Prop) (summaries : Nat → Bool → Summary)
    (implement : Nat → Implementation F E) : Prop where
  summary : ∀ name state, invariant state →
    Justifies (summaries name (implement name state).success) state (implement name state).world
  preserves : ∀ name state, invariant state → invariant (implement name state).world

omit [DecidableEq F] in
theorem handler_preserves (invariant : World F → Prop) (summaries : Nat → Bool → Summary)
    (implement : Nat → Implementation F E) (laws : Laws invariant summaries implement) :
    (handler implement).Preserves invariant := by
  intro op state initial
  cases op with
  | demand query plan =>
      by_cases ready : Ready state.known query <;>
        simpa [handler, Zkc.Modules.FactorExecution.guard, ready, Zkc.Modules.FactorExecution.handler] using initial
  | external name => exact laws.preserves name state initial

theorem execution (invariant : World F → Prop) (summaries : Nat → Bool → Summary)
    (implement : Nat → Implementation F E) (laws : Laws invariant summaries implement)
    {Γ ty} (source : Program language Γ ty) (env : Environment (Value F) Γ)
    (state : World F) (facts : List Fact) (available : List Nat)
    (valid : Valid state.values facts) (known : Known state available)
    (initial : invariant state) :
    ((rewrite summaries facts available source).denote plannedMeaning env).run (handler implement) state =
      (source.denote meaning env).run (handler implement) state := by
  induction source generalizing state facts available with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
      cases op with
      | evaluate query =>
          cases args
          by_cases ready : Ready state.known query
          · have value := inferred_value state.values facts available query valid
            simp only [rewrite, Program.denote, plannedMeaning, meaning,
              PIR.Proc.bind, PIR.Proc.run, handler, Zkc.Modules.FactorExecution.guard, if_pos ready,
              Zkc.Modules.FactorExecution.handler, PIR.Execution.follow]
            erw [value]
            erw [ih (env.push (ty := Ty.scalar) (runQuery state.values query))
              state facts available valid known initial]
            rfl
          · simp [rewrite, Program.denote, plannedMeaning, meaning, PIR.Proc.bind,
              PIR.Proc.run, handler, Zkc.Modules.FactorExecution.guard, ready, PIR.Execution.follow]
      | external name =>
          cases args
          have transfer := laws.summary name state initial
          have preserved := laws.preserves name state initial
          have factsValid := nextFacts_valid _ state _ facts transfer valid
          have inputsKnown := nextKnown_sound _ state _ available transfer known
          by_cases same : nextFacts (summaries name true) facts = nextFacts (summaries name false) facts ∧
              nextKnown (summaries name true) available = nextKnown (summaries name false) available
          · simp only [rewrite, if_pos same]
            cases success : (implement name state).success <;>
              simp only [success, same.1, same.2] at factsValid inputsKnown <;>
              simp only [same.1, same.2, Program.denote, plannedMeaning, meaning,
                PIR.Proc.bind, PIR.Proc.run, handler, Zkc.Modules.FactorExecution.guard,
                Zkc.Modules.FactorExecution.handler, Zkc.Modules.FactorExecution.returned,
                PIR.Execution.follow, success] <;>
              erw [ih _ _ _ _ factsValid inputsKnown preserved] <;> rfl
          · cases success : (implement name state).success with
            | false =>
                simp only [success] at factsValid inputsKnown
                simp only [rewrite, if_neg same, Program.denote, plannedMeaning, meaning,
                  PIR.Proc.bind, PIR.Proc.run, handler, Zkc.Modules.FactorExecution.guard,
                  Zkc.Modules.FactorExecution.handler, Zkc.Modules.FactorExecution.returned, PIR.Execution.follow,
                  PlannedOperation.result, Environment.push, success,
                  id_eq]
                erw [ih (env.push (ty := Ty.boolean) false) _ _ _ factsValid inputsKnown preserved]
                rfl
            | true =>
                simp only [success] at factsValid inputsKnown
                simp only [rewrite, if_neg same, Program.denote, plannedMeaning, meaning,
                  PIR.Proc.bind, PIR.Proc.run, handler, Zkc.Modules.FactorExecution.guard,
                  Zkc.Modules.FactorExecution.handler, Zkc.Modules.FactorExecution.returned, PIR.Execution.follow,
                  PlannedOperation.result, Environment.push, success, id_eq]
                erw [ih (env.push (ty := Ty.boolean) true) _ _ _ factsValid inputsKnown preserved]
                rfl
      | equal =>
          cases args with
          | cons left rest =>
              cases rest with
              | cons right rest =>
                  cases rest
                  simp only [rewrite, Program.denote, Operands.eval, plannedMeaning, meaning,
                    PIR.Proc.bind]
                  exact ih _ state facts available valid known initial
  | branch condition yes no ihYes ihNo =>
      simp only [rewrite, Program.denote]
      split
      · exact ihYes env state facts available valid known initial
      · exact ihNo env state facts available valid known initial
  | iterate count accumulator body next _ ihNext =>
      simp only [rewrite, Program.denote, PIR.run_bind]
      have sameBody :
          (fun value => (direct body).denote plannedMeaning (env.push value)) =
          (fun value => body.denote meaning (env.push value)) := by
        funext value
        exact direct_denote body (env.push value)
      rw [sameBody]
      have preserved := PIR.Proc.run_invariant (handler implement) invariant
        (handler_preserves invariant summaries implement laws)
        (PIR.repeatN count (fun value => body.denote meaning (env.push value)) (env accumulator))
        state initial
      cases result : (PIR.repeatN count
          (fun value => body.denote meaning (env.push value)) (env accumulator)).run
          (handler implement) state with
      | mk outcome finalState events =>
          rw [result] at preserved
          cases outcome with
          | stopped why => rfl
          | returned value =>
              simp only [PIR.Execution.follow]
              erw [ihNext (env.push value) finalState [] []
                (by simp [Valid]) (by simp [Known]) preserved]

abbrev sourceModel (implement : Nat → Implementation F E) : ExecutionModel language where
  interface := Zkc.Modules.FactorExecution.signature F
  meaning := meaning
  State := World F
  Event := E
  handler := handler implement

abbrev targetModel (implement : Nat → Implementation F E) : ExecutionModel plannedLanguage where
  interface := Zkc.Modules.FactorExecution.signature F
  meaning := plannedMeaning
  State := World F
  Event := E
  handler := handler implement

def refinement (invariant : World F → Prop) (implement : Nat → Implementation F E) (Γ : List Ty) (ty : Ty) :
    Refinement (sourceModel implement) (targetModel implement) Γ Γ ty ty where
  initial left state right other := @Eq (Environment (Value F) Γ) left right ∧ state = other ∧ invariant state
  states := Eq
  values left _ right _ := left = right
  Observation := E
  sourceView event := [event]
  targetView event := [event]

/-- The source itself produces all usable facts through the consumed module
contracts. The caller supplies no initial analysis assertions. -/
def rule (invariant : World F → Prop) (summaries : Nat → Bool → Summary)
    (implement : Nat → Implementation F E) (laws : Laws invariant summaries implement)
    (Γ : List Ty) (ty : Ty) : TransformationRule (refinement invariant implement Γ ty) where
  Certificate := Unit
  apply source _ := some (lower (rewrite summaries [] [] source))
  sound source _ plan accepted := by
    cases Option.some.inj accepted
    intro left state right other initial
    have sameEnv : (source.denote meaning left).run (handler implement) state =
        (source.denote meaning right).run (handler implement) state :=
      congrArg (fun env : Environment (Value F) Γ =>
        (source.denote meaning env).run (handler implement) state) initial.1
    have invariantState := initial.2.2
    have sameState := initial.2.1
    change state = other at sameState
    subst other
    apply PIR.Execution.Relates.of_related
    change PIR.Related Eq (fun e : E => [e]) (fun e => [e]) _ _
    change PIR.Related Eq (fun e : E => [e]) (fun e => [e])
      ((source.denote meaning left).run (handler implement) state)
      ((lower (rewrite summaries [] [] source)).run plannedMeaning (handler implement) right state)
    rw [sameEnv, lower_correct, execution invariant summaries implement laws source right state [] []
      (by simp [Valid]) (by simp [Known]) invariantState]
    exact ⟨rfl, rfl, rfl⟩

end Zkc.Compiler.FactorOptimization
