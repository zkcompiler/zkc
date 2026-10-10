import Zkc.Source.Program
import Zkc.Modules.FactorExecution

/-! Typed source requests and explicitly planned factor requests.

Coordinate references address the interpreted factor state. They are not field
constants embedded in the compiler. Both meanings retain the same readiness
guard, external calls, recoverable call results and complete stopping behavior.
-/

set_option autoImplicit false

namespace Zkc.Source.FactorQueries

open Zkc.Modules.Factor

inductive Ty where
  | scalar
  | boolean
  deriving DecidableEq, Repr

inductive Operation where
  | evaluate : Query → Operation
  | external : Nat → Operation
  | equal : Operation
  deriving DecidableEq, Repr

inductive PlannedOperation where
  | evaluate : Query → Plan → PlannedOperation
  | external : Nat → PlannedOperation
  | equal : PlannedOperation
  deriving DecidableEq, Repr

def Operation.result : Operation → Ty
  | .evaluate _ => .scalar
  | .external _ => .boolean
  | .equal => .boolean

def PlannedOperation.result : PlannedOperation → Ty
  | .evaluate _ _ => .scalar
  | .external _ => .boolean
  | .equal => .boolean

def Operation.arguments : Operation → List Ty
  | .equal => [.scalar, .scalar]
  | _ => []

def PlannedOperation.arguments : PlannedOperation → List Ty
  | .equal => [.scalar, .scalar]
  | _ => []

abbrev language : Language := ⟨Ty, Operation, Operation.arguments, Operation.result, .boolean⟩
abbrev plannedLanguage : Language :=
  ⟨Ty, PlannedOperation, PlannedOperation.arguments, PlannedOperation.result, .boolean⟩

def Value (F : Type) : Ty → Type
  | .scalar => F
  | .boolean => Bool

abbrev meaning {F : Type} [DecidableEq F] : Interpretation language (Zkc.Modules.FactorExecution.signature F) where
  Value := Value F
  condition := id
  operation
    | .evaluate query, _ => .call (.demand query .direct) .done
    | .external name, _ => .call (.external name) .done
    | .equal, .cons left (.cons right .nil) => .done (decide ((show F from left) = (show F from right)))

abbrev plannedMeaning {F : Type} [DecidableEq F] : Interpretation plannedLanguage (Zkc.Modules.FactorExecution.signature F) where
  Value := Value F
  condition := id
  operation
    | .evaluate query plan, _ => .call (.demand query plan) .done
    | .external name, _ => .call (.external name) .done
    | .equal, .cons left (.cons right .nil) => .done (decide ((show F from left) = (show F from right)))

def direct {Γ ty} : Program language Γ ty → Program plannedLanguage Γ ty
  | .ret value => .ret value
  | .stop why => .stop why
  | .letOp (.evaluate query) _ next => .letOp (.evaluate query .direct) .nil (direct next)
  | .letOp (.external name) _ next => .letOp (.external name) .nil (direct next)
  | .letOp .equal args next => .letOp .equal args (direct next)
  | .branch condition yes no => .branch condition (direct yes) (direct no)
  | .iterate count initial body next => .iterate count initial (direct body) (direct next)

theorem direct_denote {F : Type} [DecidableEq F] {Γ ty} (source : Program language Γ ty)
    (env : Environment (Value F) Γ) :
    (direct source).denote plannedMeaning env = source.denote meaning env := by
  induction source with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
      cases op with
      | evaluate query =>
          cases args
          simp only [direct, Program.denote]
          congr 1
          funext value
          exact ih (env.push value)
      | external name =>
          cases args
          simp only [direct, Program.denote]
          congr 1
          funext value
          exact ih (env.push value)
      | equal =>
          cases args with
          | cons left rest =>
              cases rest with
              | cons right rest =>
                  cases rest
                  simp only [direct, Program.denote, Operands.eval, plannedMeaning, meaning,
                    PIR.Proc.bind]
                  exact ih _
  | branch condition yes no ihYes ihNo => simp only [direct, Program.denote, ihYes, ihNo]
  | iterate count initial body next ihBody ihNext =>
      simp only [direct, Program.denote]
      have sameBody :
          (fun value => (direct body).denote plannedMeaning (env.push value)) =
          (fun value => body.denote meaning (env.push value)) := by
        funext value
        exact ihBody (env.push value)
      rw [sameBody]
      congr 1
      funext value
      exact ihNext (env.push value)

end Zkc.Source.FactorQueries
