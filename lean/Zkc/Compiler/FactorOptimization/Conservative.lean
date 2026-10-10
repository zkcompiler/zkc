import Zkc.Compiler.FactorOptimization
import Zkc.Compiler.Analysis.FactorMerge

/-! Factor planning with one continuation for both external outcomes.

Only facts and coordinates available after either outcome survive the merge.
This trades path precision for unchanged control structure; it does not merge
runtime states or alter the returned Boolean. The original specialized rule
remains available separately.
-/

set_option autoImplicit false

namespace Zkc.Compiler.FactorOptimization.Conservative

open Source Source.FactorQueries FactorReuse Modules.Factor Modules.FactorState

def rewrite (summaries : Nat → Bool → Summary) (facts : List Fact) (available : List Nat)
    {Γ ty} : Program language Γ ty → Program plannedLanguage Γ ty
  | .ret value => .ret value
  | .stop why => .stop why
  | .letOp (.evaluate query) _ next =>
      .letOp (.evaluate query (infer facts available query)) .nil
        (rewrite summaries facts available next)
  | .letOp (.external name) _ next =>
      .letOp (.external name) .nil
        (rewrite summaries (FactorMerge.facts (summaries name) facts)
          (FactorMerge.available (summaries name) available) next)
  | .letOp .equal args next => .letOp .equal args (rewrite summaries facts available next)
  | .branch condition yes no => .branch condition
      (rewrite summaries facts available yes) (rewrite summaries facts available no)
  | .iterate count initial body next =>
      .iterate count initial (direct body) (rewrite summaries [] [] next)

variable {F E : Type} [DecidableEq F]

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
          have factsValid := FactorMerge.facts_valid (summaries name) state _
            (implement name state).success transfer facts valid
          have inputsKnown := FactorMerge.available_known (summaries name) state _
            (implement name state).success transfer available known
          simp only [rewrite, Program.denote, plannedMeaning, meaning,
            PIR.Proc.bind, PIR.Proc.run, handler, Zkc.Modules.FactorExecution.guard,
            Zkc.Modules.FactorExecution.handler, Zkc.Modules.FactorExecution.returned,
            PIR.Execution.follow]
          erw [ih _ _ _ _ factsValid inputsKnown preserved]
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

end Zkc.Compiler.FactorOptimization.Conservative
