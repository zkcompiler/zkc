import Std

/-! Finite typed contexts shared by source formation and execution plans.

Variable positions are de Bruijn indices: position zero is the most recently
bound value. Semantic values are supplied separately from portable syntax.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty : Type}

/-- Membership in an ordered typed context. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {ty : Ty} : Var (ty :: Γ) ty
  | there {Γ : List Ty} {ty head : Ty} : Var Γ ty → Var (head :: Γ) ty
  deriving Repr

def Var.index {Γ : List Ty} {ty : Ty} : Var Γ ty → Nat
  | .here => 0
  | .there v => v.index + 1

/-- Resolve an external position against its required type, without defaults. -/
def Var.decode [DecidableEq Ty] : (Γ : List Ty) → (ty : Ty) → Nat → Option (Var Γ ty)
  | [], _, _ => none
  | head :: _, ty, 0 => if h : head = ty then h ▸ some .here else none
  | _ :: Γ, ty, n + 1 => (decode Γ ty n).map .there

@[simp] theorem Var.decode_index [DecidableEq Ty] {Γ : List Ty} {ty : Ty}
    (v : Var Γ ty) : Var.decode Γ ty v.index = some v := by
  induction v with
  | here => simp [decode, index]
  | there v ih => simp [decode, index, ih]

/-- A heterogeneous list; its order is part of the binding contract. -/
inductive Values (Value : Ty → Type) : List Ty → Type where
  | nil : Values Value []
  | cons {ty : Ty} {Γ : List Ty} : Value ty → Values Value Γ → Values Value (ty :: Γ)

def Values.get {Value : Ty → Type} {Γ : List Ty} {ty : Ty}
    (values : Values Value Γ) (v : Var Γ ty) : Value ty :=
  match v, values with
  | .here, .cons value _ => value
  | .there tail, .cons _ values => values.get tail

abbrev Environment (Value : Ty → Type) (Γ : List Ty) :=
  {ty : Ty} → Var Γ ty → Value ty

def Environment.push {Value : Ty → Type} {Γ : List Ty} {ty : Ty}
    (env : Environment Value Γ) (value : Value ty) : Environment Value (ty :: Γ)
  | _, .here => value
  | _, .there v => env v

/-- Bind ordered results in front of the retained caller context. -/
def Environment.prepend {Value : Ty → Type} {Γ Δ : List Ty}
    (env : Environment Value Γ) (values : Values Value Δ) : Environment Value (Δ ++ Γ) :=
  match values with
  | .nil => env
  | .cons value rest => Environment.push (Environment.prepend env rest) value

/-- Preserve a variable while adding a prefix to its context. -/
def Var.weakenPrefix {Γ : List Ty} {ty : Ty} (extra : List Ty)
    (value : Var Γ ty) : Var (extra ++ Γ) ty :=
  match extra with
  | [] => value
  | _ :: rest => .there (value.weakenPrefix rest)

@[simp] theorem Environment.prepend_weakenPrefix {Value : Ty → Type} {Γ Δ : List Ty}
    {ty : Ty} (env : Environment Value Γ) (values : Values Value Δ) (value : Var Γ ty) :
    env.prepend values (value.weakenPrefix Δ) = env value := by
  induction values with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- An explicit, ordered map of operands into the surrounding context. -/
abbrev Operands (Γ : List Ty) := Values (Var Γ)

def Operands.eval {Value : Ty → Type} {Γ args : List Ty}
    (env : Environment Value Γ) : Operands Γ args → Values Value args
  | .nil => .nil
  | .cons v tail => .cons (env v) (Operands.eval env tail)

theorem Operands.get_eval {Value : Ty → Type} {Γ args : List Ty} {ty : Ty}
    (env : Environment Value Γ) (operands : Operands Γ args) (value : Var args ty) :
    (Operands.eval env operands).get value = env (operands.get value) := by
  induction operands with
  | nil => cases value
  | cons head tail ih => cases value with
    | here => rfl
    | there value => exact ih value

abbrev Renaming (Γ Δ : List Ty) := {ty : Ty} → Var Γ ty → Var Δ ty

def Renaming.lift {Γ Δ : List Ty} {ty : Ty} (rename : Renaming Γ Δ) :
    Renaming (ty :: Γ) (ty :: Δ)
  | _, .here => .here
  | _, .there v => .there (rename v)

def Operands.rename {Γ Δ args : List Ty} (rename : Renaming Γ Δ) :
    Operands Γ args → Operands Δ args
  | .nil => .nil
  | .cons v tail => .cons (rename v) (Operands.rename rename tail)

theorem Operands.eval_rename {Value : Ty → Type} {Γ Δ args : List Ty}
    (rename : Renaming Γ Δ) (env : Environment Value Δ) (operands : Operands Γ args) :
    Operands.eval env (Operands.rename rename operands) =
      Operands.eval (fun v => env (rename v)) operands := by
  induction operands with
  | nil => rfl
  | cons v tail ih => simp only [Operands.rename, eval, ih]

theorem Environment.push_rename {Value : Ty → Type} {Γ Δ : List Ty} {ty : Ty}
    (rename : Renaming Γ Δ) (env : Environment Value Δ) (value : Value ty) :
    @Eq (Environment Value (ty :: Γ))
      (fun v => env.push value (Renaming.lift rename v))
      (Environment.push (fun v => env (rename v)) value) := by
  funext result v
  cases v <;> rfl

end Zkc.Source
