module

public import Zkc.Source.Context

@[expose] public section

/-! Reusable context operations for ordered result tuples and explicit captures. -/
set_option autoImplicit false
namespace Zkc.Source

variable {Ty : Type}

def Values.append {Value : Ty → Type} {Γ Δ : List Ty} :
    Values Value Γ → Values Value Δ → Values Value (Γ ++ Δ)
  | .nil, right => right
  | .cons value rest, right => .cons value (rest.append right)

/-- Separate an explicitly typed result prefix from the retained suffix. -/
def Values.split {Value : Ty → Type} (added : List Ty) {Γ : List Ty}
    (values : Values Value (added ++ Γ)) : Values Value added × Values Value Γ :=
  match added, values with
  | [], values => (.nil, values)
  | _ :: rest, .cons value values =>
      let parts := Values.split rest values
      (.cons value parts.1, parts.2)

@[simp] theorem Values.split_append {Value : Ty → Type} {Γ Δ : List Ty}
    (first : Values Value Γ) (rest : Values Value Δ) :
    Values.split Γ (first.append rest) = (first, rest) := by
  induction first with
  | nil => rfl
  | cons value tail ih => simp only [Values.append, Values.split, ih]

@[simp] theorem Values.append_split {Value : Ty → Type} (added : List Ty) {Γ : List Ty}
    (values : Values Value (added ++ Γ)) :
    (Values.split added values).1.append (Values.split added values).2 = values := by
  induction added with
  | nil => rfl
  | cons ty rest ih =>
    cases values with
    | cons value tail =>
      change Values.cons value
        ((Values.split rest tail).1.append (Values.split rest tail).2) = .cons value tail
      rw [ih]

/-- Capture a complete context in its declaration order. -/
def Operands.identity : (Γ : List Ty) → Operands Γ Γ
  | [] => .nil
  | _ :: rest => .cons .here ((identity rest).rename (fun value => .there value))

theorem Operands.get_rename {Γ Δ args : List Ty} {ty : Ty}
    (rename : Renaming Γ Δ) (operands : Operands Γ args) (reference : Var args ty) :
    (operands.rename rename).get reference = rename (operands.get reference) := by
  induction operands with
  | nil => cases reference
  | cons head tail ih =>
    cases reference with
    | here => rfl
    | there reference => exact ih reference

@[simp] theorem Operands.identity_get {Γ : List Ty} {ty : Ty} (reference : Var Γ ty) :
    (Operands.identity Γ).get reference = reference := by
  induction reference with
  | here => rfl
  | there reference ih =>
    simp only [identity, Values.get, get_rename, ih]

/-- Reify an environment as an ordered tuple, without inventing missing values. -/
def Environment.toValues {Value : Ty → Type} {Γ : List Ty}
    (env : Environment Value Γ) : Values Value Γ :=
  Operands.eval env (Operands.identity Γ)

@[simp] theorem Environment.toValues_get {Value : Ty → Type} {Γ : List Ty} {ty : Ty}
    (env : Environment Value Γ) (reference : Var Γ ty) : env.toValues.get reference = env reference := by
  simp only [toValues, Operands.get_eval, Operands.identity_get]

theorem Environment.toValues_environment {Value : Ty → Type} {Γ : List Ty}
    (env : Environment Value Γ) : @Eq (Environment Value Γ) env.toValues.get env := by
  funext ty reference
  exact toValues_get env reference

theorem Operands.get_eval_identity {Value : Ty → Type} {Γ : List Ty}
    (env : Environment Value Γ) :
    @Eq (Environment Value Γ) (Operands.eval env (Operands.identity Γ)).get env :=
  Environment.toValues_environment env

/-- Lift a renaming below an ordered result prefix. -/
def Renaming.liftPrefix {Ty : Type} {Γ Δ : List Ty} (added : List Ty)
    (rename : Renaming Γ Δ) : Renaming (added ++ Γ) (added ++ Δ) :=
  match added with
  | [] => rename
  | _ :: rest => Renaming.lift (Renaming.liftPrefix rest rename)

theorem Environment.prepend_rename {Ty : Type} {Value : Ty → Type}
    {Γ Δ added : List Ty} (rename : Renaming Γ Δ) (env : Environment Value Δ)
    (values : Values Value added) :
    @Eq (Environment Value (added ++ Γ))
      (fun value => env.prepend values (Renaming.liftPrefix added rename value))
      (Environment.prepend (fun value => env (rename value)) values) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    funext ty reference
    cases reference with
    | here => rfl
    | there reference => exact congrFun (congrFun ih _) reference


variable {Ty : Type} {Value : Ty → Type}

/-- Embed a reference profile's single result in the canonical result list. -/
def Values.singleton {ty : Ty} (value : Value ty) : Values Value [ty] :=
  .cons value .nil

@[simp] theorem Values.get_singleton {ty : Ty} (value : Value ty) :
    (Values.singleton value).get .here = value := rfl

@[simp] theorem Values.singleton_get {ty : Ty} (values : Values Value [ty]) :
    Values.singleton (values.get .here) = values := by
  cases values with
  | cons value rest => cases rest; rfl

theorem Environment.prepend_singleton {Γ : List Ty} {ty : Ty}
    (env : Environment Value Γ) (value : Value ty) :
    @Eq (Environment Value (ty :: Γ))
      (env.prepend (Values.singleton value)) (env.push value) := rfl

theorem Values.get_cons {Γ : List Ty} {ty : Ty}
    (value : Value ty) (values : Values Value Γ) :
    @Eq (Environment Value (ty :: Γ)) (Values.cons value values).get
      (Environment.push values.get value) := by
  funext sort ref
  cases ref <;> rfl

@[simp] theorem Operands.rename_identity {Γ args : List Ty} (operands : Operands Γ args) :
    operands.rename (fun value => value) = operands := by
  induction operands with
  | nil => rfl
  | cons value tail ih => simp only [Operands.rename, ih]

theorem Operands.rename_comp {Γ Δ Ξ args : List Ty} (first : Renaming Γ Δ)
    (second : Renaming Δ Ξ) (operands : Operands Γ args) :
    (operands.rename first).rename second = operands.rename (fun value => second (first value)) := by
  induction operands with
  | nil => rfl
  | cons value tail ih => simp only [Operands.rename, ih]

theorem Renaming.liftPrefix_identity {Γ : List Ty} (added : List Ty) :
    @Eq (Renaming (added ++ Γ) (added ++ Γ))
      (liftPrefix added (fun value => value)) (fun value => value) := by
  induction added with
  | nil => rfl
  | cons ty rest ih =>
    funext sort reference
    cases reference with
    | here => rfl
    | there reference => exact congrArg Var.there (congrFun (congrFun ih _) reference)

theorem Renaming.liftPrefix_comp {Γ Δ Ξ : List Ty} (added : List Ty)
    (first : Renaming Γ Δ) (second : Renaming Δ Ξ) :
    @Eq (Renaming (added ++ Γ) (added ++ Ξ))
      (fun value => liftPrefix added second (liftPrefix added first value))
      (liftPrefix added (fun value => second (first value))) := by
  induction added with
  | nil => rfl
  | cons ty rest ih =>
    funext sort reference
    cases reference with
    | here => rfl
    | there reference => exact congrArg Var.there (congrFun (congrFun ih _) reference)

end Zkc.Source
