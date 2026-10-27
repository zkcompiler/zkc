module

public import Zkc.Executable.NativeLaws

@[expose] public section

/-! Resource bounds and binding-preserving transport for actual native local
functions. These theorems are independent of an Instruction interpreter. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction Zkc.Source
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## Helper costs by evaluation -/

mutual
/-- At most what a local body without iterations charges, by evaluation of its
structure: a conditional charges itself and the dearer region. -/
def Steps.costBound : List Step → Option Nat
  | [] => some 0
  | step :: rest =>
      match Step.costBound step, Steps.costBound rest with
      | some first, some others => some (first + others)
      | _, _ => none

/-- At most what one local instruction charges, with its regions. -/
def Step.costBound : Step → Option Nat
  | .operation .. | .constant .. | .stop .. | .yield _ | .ret _ => some 1
  | .cond _ _ _ yes no _ =>
      match Steps.costBound yes, Steps.costBound no with
      | some first, some second => some (1 + max first second)
      | _, _ => none
  | .iterate .. => none
  | .unsupported _ => some 0
end

section HelperCosts
variable (vocabulary : Vocabulary) (validator : Validator)

/-- What one evaluated step charges. -/
def Stepped.cost : Stepped F G → Nat
  | .next _ cost => cost
  | .done result => result.cost

mutual
theorem evalSteps_cost_le :
    ∀ (steps : List Step) (bound : Nat) (env : Env F G), Steps.costBound steps = some bound →
      (evalSteps vocabulary validator steps env).cost ≤ bound
  | [], bound, env, bounded => by
      simp only [Steps.costBound, Option.some.injEq] at bounded
      subst bounded
      simp [evalSteps, Evaluated.cost]
  | step :: rest, bound, env, bounded => by
      simp only [Steps.costBound] at bounded
      cases firstEq : Step.costBound step with
      | none => simp [firstEq] at bounded
      | some first =>
          cases othersEq : Steps.costBound rest with
          | none => simp [firstEq, othersEq] at bounded
          | some others =>
              simp only [firstEq, othersEq, Option.some.injEq] at bounded
              subst bounded
              have stepped := evalStep_cost_le step first env firstEq
              cases stepEq : evalStep vocabulary validator step env with
              | next env' cost =>
                  rw [stepEq] at stepped
                  simp only [evalSteps, stepEq]
                  have restCost := evalSteps_cost_le rest others env' othersEq
                  cases evaluated : evalSteps vocabulary validator rest env' with
                  | values results cost' =>
                      rw [evaluated] at restCost
                      simp only [Stepped.cost, Evaluated.after, Evaluated.cost] at stepped restCost ⊢
                      omega
                  | stopped cause cost' =>
                      rw [evaluated] at restCost
                      simp only [Stepped.cost, Evaluated.after, Evaluated.cost] at stepped restCost ⊢
                      omega
              | done result =>
                  rw [stepEq] at stepped
                  simp only [evalSteps, stepEq]
                  simp only [Stepped.cost] at stepped
                  omega

theorem evalStep_cost_le :
    ∀ (step : Step) (bound : Nat) (env : Env F G), Step.costBound step = some bound →
      (evalStep vocabulary validator step env).cost ≤ bound
  | .operation site binding parameters inputs outputs, bound, env, bounded => by
      simp only [Step.costBound, Option.some.injEq] at bounded
      subst bounded
      simp only [evalStep]
      split
      · split
        · split <;> simp [Stepped.cost, Evaluated.cost]
        · simp [Stepped.cost, Evaluated.cost]
      · simp [Stepped.cost, Evaluated.cost]
  | .constant site output value, bound, env, bounded => by
      simp only [Step.costBound, Option.some.injEq] at bounded
      subst bounded
      simp [evalStep, Stepped.cost]
  | .stop site reason, bound, env, bounded => by
      simp only [Step.costBound, Option.some.injEq] at bounded
      subst bounded
      simp only [evalStep]
      split <;> simp [Stepped.cost, Evaluated.cost]
  | .yield values, bound, env, bounded => by
      simp only [Step.costBound, Option.some.injEq] at bounded
      subst bounded
      simp only [evalStep]
      split <;> simp [Stepped.cost, Evaluated.cost]
  | .ret values, bound, env, bounded => by
      simp only [Step.costBound, Option.some.injEq] at bounded
      subst bounded
      simp only [evalStep]
      split <;> simp [Stepped.cost, Evaluated.cost]
  | .unsupported name, bound, env, bounded => by
      simp only [Step.costBound, Option.some.injEq] at bounded
      subst bounded
      simp [evalStep, Stepped.cost, Evaluated.cost]
  | .iterate .., _, _, bounded => by simp [Step.costBound] at bounded
  | .cond site condition captures yes no outputs, bound, env, bounded => by
      simp only [Step.costBound] at bounded
      cases yesEq : Steps.costBound yes with
      | none => simp [yesEq] at bounded
      | some first =>
          cases noEq : Steps.costBound no with
          | none => simp [yesEq, noEq] at bounded
          | some second =>
              simp only [yesEq, noEq, Option.some.injEq] at bounded
              subst bounded
              have region : ∀ (taken : List Step) (most : Nat),
                  (∀ captured : Env F G, (evalSteps vocabulary validator taken captured).cost ≤ most) →
                    most ≤ max first second →
                  ∀ (captured : Env F G),
                    (match evalSteps vocabulary validator taken captured with
                      | .values results cost =>
                          if outputs.length = results.length then Stepped.next (outputs.zip results ++ env) (1 + cost)
                          else .done (.stopped .contract (1 + cost))
                      | .stopped cause cost => .done (.stopped cause (1 + cost))).cost ≤ 1 + max first second := by
                intro taken most takenBound smaller captured
                have takenCost := takenBound captured
                cases evaluated : evalSteps vocabulary validator taken captured with
                | values results cost =>
                    rw [evaluated] at takenCost
                    simp only [Evaluated.cost] at takenCost
                    dsimp only
                    split <;> simp only [Stepped.cost, Evaluated.cost] <;> omega
                | stopped cause cost =>
                    rw [evaluated] at takenCost
                    simp only [Evaluated.cost] at takenCost
                    simp only [Stepped.cost, Evaluated.cost]
                    omega
              have yesCost := fun captured => evalSteps_cost_le yes first captured yesEq
              have noCost := fun captured => evalSteps_cost_le no second captured noEq
              simp only [evalStep]
              split
              · exact region yes first yesCost (le_max_left _ _) _
              · exact region no second noCost (le_max_right _ _) _
              · simp [Stepped.cost, Evaluated.cost]
end

/-- At most what a helper call's body charges, by evaluation of the local
function's structure. -/
def helperBound (name : String) : Option Nat :=
  (validator.function? name).bind fun function => Steps.costBound function.body

theorem helperCost_le {name : String} {bound : Nat} (bounded : helperBound validator name = some bound)
    (arguments : List (Value F G)) : helperCost vocabulary validator name arguments ≤ bound := by
  unfold helperBound at bounded
  unfold helperCost Validator.evaluateCall
  cases functionEq : validator.function? name with
  | none => simp [functionEq] at bounded
  | some function =>
      simp only [functionEq, Option.bind_some] at bounded
      simp only
      split
      · exact evalSteps_cost_le vocabulary validator function.body bound _ bounded
      · simp [Evaluated.cost]

end HelperCosts

/-! ## Helper evaluation across validators -/

mutual
/-- The binding symbols a local body applies, its regions' included. -/
def Steps.bindings : List Step → List String
  | [] => []
  | step :: rest => Step.bindings step ++ Steps.bindings rest

def Step.bindings : Step → List String
  | .operation _ binding _ _ _ => [binding]
  | .cond _ _ _ yes no _ => Steps.bindings yes ++ Steps.bindings no
  | .iterate _ _ _ _ _ _ body _ => Steps.bindings body
  | _ => []
end

section Transfer
variable (vocabulary : Vocabulary)

mutual
/-- A local body evaluates alike under two validators that resolve its
bindings alike. -/
theorem evalSteps_congr {validator validator' : Validator} :
    ∀ (steps : List Step), (∀ binding ∈ Steps.bindings steps, validator.binding? binding = validator'.binding? binding) →
      ∀ (env : Env F G), evalSteps vocabulary validator steps env = evalSteps vocabulary validator' steps env
  | [], _, env => rfl
  | step :: rest, agree, env => by
      simp only [evalSteps]
      rw [evalStep_congr step (fun binding member => agree binding (by
        simp only [Steps.bindings]; exact List.mem_append_left _ member)) env]
      split
      · rename_i env' cost _
        rw [evalSteps_congr rest (fun binding member => agree binding (by
          simp only [Steps.bindings]; exact List.mem_append_right _ member)) env']
      · rfl

theorem evalStep_congr {validator validator' : Validator} :
    ∀ (step : Step), (∀ binding ∈ Step.bindings step, validator.binding? binding = validator'.binding? binding) →
      ∀ (env : Env F G), evalStep vocabulary validator step env = evalStep vocabulary validator' step env
  | .operation site binding parameters inputs outputs, agree, env => by
      simp only [evalStep, agree binding (by simp [Step.bindings])]
  | .constant .., _, _ => rfl
  | .stop .., _, _ => rfl
  | .yield _, _, _ => rfl
  | .ret _, _, _ => rfl
  | .unsupported _, _, _ => rfl
  | .cond site condition captures yes no outputs, agree, env => by
      have yesAgree := fun captured => evalSteps_congr (validator := validator) (validator' := validator') yes
        (fun binding member => agree binding (by simp only [Step.bindings]; exact List.mem_append_left _ member))
        captured
      have noAgree := fun captured => evalSteps_congr (validator := validator) (validator' := validator') no
        (fun binding member => agree binding (by simp only [Step.bindings]; exact List.mem_append_right _ member))
        captured
      simp only [evalStep, yesAgree, noAgree]
  | .iterate site induction lower upper carried captures body outputs, agree, env => by
      have bodyAgree := fun inner => evalSteps_congr (validator := validator) (validator' := validator') body
        (fun binding member => agree binding (by simp only [Step.bindings]; exact member)) inner
      simp only [evalStep, bodyAgree]
end

/-- Two validators whose local function `name` is the same body, with its
bindings resolved alike. -/
def FunctionAgrees (validator validator' : Validator) (name : String) : Prop :=
  validator.function? name = validator'.function? name ∧
    ∀ function, validator.function? name = some function →
      ∀ binding ∈ Steps.bindings function.body, validator.binding? binding = validator'.binding? binding

/-- Whether two validators resolve the bindings of the local function `name`
alike, decided by evaluation. -/
def bindingsAgree (validator validator' : Validator) (name : String) : Bool :=
  match validator.function? name with
  | some function => (Steps.bindings function.body).all fun binding =>
      decide (validator.binding? binding = validator'.binding? binding)
  | none => true

/-- The same local function, with its bindings resolved alike, agrees. -/
theorem functionAgrees_of {validator validator' : Validator} {name : String}
    (same : validator.function? name = validator'.function? name)
    (bindings : bindingsAgree validator validator' name = true) : FunctionAgrees validator validator' name := by
  refine ⟨same, fun function found binding member => ?_⟩
  unfold bindingsAgree at bindings
  rw [found] at bindings
  simpa using (List.all_eq_true.mp bindings) binding member

theorem evaluateCall_agrees {validator validator' : Validator} {name : String}
    (agrees : FunctionAgrees validator validator' name) (arguments : List (Value F G)) :
    validator.evaluateCall vocabulary name arguments = validator'.evaluateCall vocabulary name arguments := by
  obtain ⟨same, bindings⟩ := agrees
  unfold Validator.evaluateCall
  rw [← same]
  cases found : validator.function? name with
  | none => rfl
  | some function =>
      simp only
      rw [evalSteps_congr vocabulary function.body (bindings function found)]

theorem helperCost_agrees {validator validator' : Validator} {name : String}
    (agrees : FunctionAgrees validator validator' name) (arguments : List (Value F G)) :
    helperCost vocabulary validator name arguments = helperCost vocabulary validator' name arguments := by
  unfold helperCost
  rw [evaluateCall_agrees vocabulary agrees]

theorem prepared_agrees {validator validator' : Validator} {name : String} (agrees : FunctionAgrees validator validator' name)
    {table : Structured.Evaluation.Meanings F G Structured.closedInterface}
    (prepared : Prepared vocabulary validator table name) : Prepared vocabulary validator' table name := by
  intro callee found arguments length sorted
  obtain ⟨same, bindings⟩ := agrees
  have found' : validator.function? name = some callee := by rw [same]; exact found
  have result := prepared callee found' arguments length sorted
  rwa [evalSteps_congr vocabulary callee.body (bindings callee found')] at result

end Transfer

end Zkc.Executable
