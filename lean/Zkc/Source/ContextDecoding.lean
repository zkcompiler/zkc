module

public import Zkc.Source.Context

@[expose] public section

/-! Shared checked context lookup and operand formation.

Every declared operand is checked independently of runtime reachability.
Program and region structure are owned by their respective adapters.
-/

set_option autoImplicit false

namespace Zkc.Source

inductive FormationError (Ty : Type) where
  | invalidOperand (index : Nat) (expected : Ty)
  | operandCount (expected actual : Nat)
  deriving DecidableEq, Repr

variable {Ty : Type} [DecidableEq Ty]

def decodeVariable (Γ : List Ty) (ty : Ty) (index : Nat) :
    Except (FormationError Ty) (Var Γ ty) :=
  match Var.decode Γ ty index with
  | some value => .ok value
  | none => .error (.invalidOperand index ty)

def Operands.indices {Γ args : List Ty} : Operands Γ args → List Nat
  | .nil => []
  | .cons v tail => v.index :: Operands.indices tail

def decodeOperands (Γ : List Ty) : (args : List Ty) → List Nat →
    Except (FormationError Ty) (Operands Γ args)
  | [], [] => .ok .nil
  | ty :: args, index :: indices => do
    let value ← decodeVariable Γ ty index
    let tail ← decodeOperands Γ args indices
    pure (.cons value tail)
  | args, indices => .error (.operandCount args.length indices.length)

@[simp] theorem decodeVariable_index {Γ : List Ty} {ty : Ty} (v : Var Γ ty) :
    decodeVariable Γ ty v.index = .ok v := by
  simp [decodeVariable]

@[simp] theorem decodeOperands_indices {Γ args : List Ty} (operands : Operands Γ args) :
    decodeOperands Γ args (Operands.indices operands) = .ok operands := by
  induction operands with
  | nil => rfl
  | cons v tail ih => simp [Operands.indices, decodeOperands, ih]; rfl

/-- Successful context lookup retains the exact raw variable position. -/
theorem Var.index_of_decode {Ty : Type} [DecidableEq Ty] {Γ : List Ty} {ty : Ty}
    {index : Nat} {value : Var Γ ty} (accepted : Var.decode Γ ty index = some value) :
    value.index = index := by
  induction Γ generalizing index with
  | nil => simp [Var.decode] at accepted
  | cons head Γ ih =>
    cases index with
    | zero =>
      simp only [Var.decode] at accepted
      split at accepted
      next same =>
        subst head
        cases accepted
        rfl
      next => contradiction
    | succ index =>
      cases decoded : Var.decode Γ ty index with
      | none => simp [Var.decode, decoded] at accepted
      | some tail =>
        simp only [Var.decode, decoded, Option.map_some, Option.some.injEq] at accepted
        subst value
        exact congrArg Nat.succ (ih decoded)

/-- The checked operand adapter preserves successful variable positions. -/
theorem index_of_decodeVariable {Ty : Type} [DecidableEq Ty] {Γ : List Ty} {ty : Ty}
    {index : Nat} {value : Var Γ ty} (accepted : decodeVariable Γ ty index = .ok value) :
    value.index = index := by
  unfold decodeVariable at accepted
  cases decoded : Var.decode Γ ty index with
  | none => simp [decoded] at accepted
  | some decodedValue =>
    simp only [decoded, Except.ok.injEq] at accepted
    subst value
    exact Var.index_of_decode decoded

/-- Successful operand formation retains every raw position in its original order. -/
theorem indices_of_decodeOperands {Ty : Type} [DecidableEq Ty] {Γ args : List Ty}
    {indices : List Nat} {operands : Operands Γ args}
    (accepted : decodeOperands Γ args indices = .ok operands) :
    Operands.indices operands = indices := by
  induction args generalizing indices with
  | nil =>
    cases indices with
    | nil => cases accepted; rfl
    | cons index indices => simp [decodeOperands] at accepted
  | cons ty args ih =>
    cases indices with
    | nil => simp [decodeOperands] at accepted
    | cons index indices =>
      cases decodedValue : decodeVariable Γ ty index with
      | error error =>
        simp [decodeOperands, decodedValue] at accepted
        cases accepted
      | ok value =>
        cases decodedTail : decodeOperands Γ args indices with
        | error error =>
          simp [decodeOperands, decodedValue, decodedTail] at accepted
          cases accepted
        | ok tail =>
          simp [decodeOperands, decodedValue, decodedTail] at accepted
          cases accepted
          simp [Operands.indices, index_of_decodeVariable decodedValue, ih decodedTail]

end Zkc.Source
