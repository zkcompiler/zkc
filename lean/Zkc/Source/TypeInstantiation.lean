import Zkc.Source.Region

/-! Type substitution for structured source, before domain implementation
selection. Static instantiation changes types and preserves control, operation
identities, operands, and complete process meaning. The substitution need not
be injective: distinct parameters may select the same mathematical domain.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty Target : Type}

def Var.instantiate (select : Ty → Target) {Γ : List Ty} {ty : Ty} :
    Var Γ ty → Var (Γ.map select) (select ty)
  | .here => .here
  | .there value => .there (value.instantiate select)

@[simp] theorem Var.index_instantiate (select : Ty → Target)
    {Γ : List Ty} {ty : Ty} (value : Var Γ ty) :
    (value.instantiate select).index = value.index := by
  induction value <;> simp_all [instantiate, index]

def Values.instantiate (select : Ty → Target) {Value : Target → Type} {Γ : List Ty} :
    Values (fun ty => Value (select ty)) Γ → Values Value (Γ.map select)
  | .nil => .nil
  | .cons value tail => .cons value (tail.instantiate select)

def Operands.instantiate (select : Ty → Target) {Γ args : List Ty} :
    Operands Γ args → Operands (Γ.map select) (args.map select)
  | .nil => .nil
  | .cons value tail => .cons (value.instantiate select) (Operands.instantiate select tail)

def Environment.pullback (select : Ty → Target) {Value : Target → Type} {Γ : List Ty}
    (env : Environment Value (Γ.map select)) : Environment (fun ty => Value (select ty)) Γ :=
  fun value => env (value.instantiate select)

theorem Environment.pullback_push (select : Ty → Target) {Value : Target → Type}
    {Γ : List Ty} {ty : Ty} (env : Environment Value (Γ.map select))
    (value : Value (select ty)) :
    @Eq (Environment (fun ty => Value (select ty)) (ty :: Γ))
      (Environment.pullback select (Γ := ty :: Γ) (Environment.push env value))
      (Environment.push (Environment.pullback select env) value) := by
  funext result v
  cases v <;> rfl

theorem Operands.eval_instantiate (select : Ty → Target) {Value : Target → Type}
    {Γ args : List Ty} (operands : Operands Γ args)
    (env : Environment Value (Γ.map select)) :
    (Operands.instantiate select operands).eval env =
      (operands.eval (env.pullback select)).instantiate select := by
  induction operands with
  | nil => rfl
  | cons _ _ ih => simp only [instantiate, eval, Values.instantiate, ih]; rfl

abbrev Language.instantiate (language : Language) (select : language.Ty → Target) : Language where
  Ty := Target
  Op := language.Op
  arguments op := (language.arguments op).map select
  result op := select (language.result op)
  condition := select language.condition

variable {language : Language} {interface : PIR.Signature}

/-- Source meaning at a selected type environment, defined directly from the
selected operation semantics rather than from a transformed region. -/
abbrev Interpretation.pullback (select : language.Ty → Target)
    (meaning : Interpretation (language.instantiate select) interface) :
    Interpretation language interface where
  Value ty := meaning.Value (select ty)
  condition := meaning.condition
  operation op args := meaning.operation op (args.instantiate select)

def Region.instantiate (select : language.Ty → Target) {Γ : List language.Ty}
    {ty : language.Ty} :
    Region language Γ ty → Region (language.instantiate select) (Γ.map select) (select ty)
  | .ret value => .ret (value.instantiate select)
  | .stop reason => .stop reason
  | .letOp op arguments next =>
      .letOp op (Operands.instantiate select arguments) (next.instantiate select)
  | .branch condition yes no =>
      .branch (condition.instantiate select) (yes.instantiate select) (no.instantiate select)
  | .iterate count initial body next =>
      .iterate count (initial.instantiate select) (body.instantiate select) (next.instantiate select)
  | .bind body next => .bind (body.instantiate select) (next.instantiate select)

theorem Region.denote_instantiate (select : language.Ty → Target)
    (meaning : Interpretation (language.instantiate select) interface)
    {Γ : List language.Ty} {ty : language.Ty} (body : Region language Γ ty)
    (env : Environment meaning.Value (Γ.map select)) :
    (body.instantiate select).denote meaning env =
      body.denote (meaning.pullback select) (env.pullback select) := by
  induction body with
  | ret => rfl
  | stop => rfl
  | letOp op arguments next ih =>
      simp only [instantiate, denote, Interpretation.pullback]
      rw [Operands.eval_instantiate select arguments env]
      congr 1
      funext value
      rw [ih, Environment.pullback_push]
  | branch condition yes no yesIH noIH =>
      simp only [instantiate, denote, yesIH, noIH]
      rfl
  | iterate count initial body next bodyIH nextIH =>
      simp only [instantiate, denote]
      have same :
          (fun value => (body.instantiate select).denote meaning (env.push value)) =
          (fun value => body.denote (meaning.pullback select)
            (Environment.push (env.pullback select) value)) := by
        funext value
        rw [bodyIH, Environment.pullback_push]
      rw [same]
      congr 1
      funext value
      rw [nextIH, Environment.pullback_push]
  | bind body next bodyIH nextIH =>
      simp only [instantiate, denote, bodyIH]
      congr 1
      funext value
      rw [nextIH, Environment.pullback_push]

/-- This is equality of full executions, including rejected/aborted/exhausted
post-state and event prefix, not only returned values. Backend conformance is
a separate obligation of the selected operation meanings and handler. -/
theorem Region.run_instantiate (select : language.Ty → Target)
    (meaning : Interpretation (language.instantiate select) interface)
    {S E : Type} (handler : PIR.Handler interface S E)
    {Γ : List language.Ty} {ty : language.Ty} (body : Region language Γ ty)
    (env : Environment meaning.Value (Γ.map select)) (state : S) :
    ((body.instantiate select).denote meaning env).run handler state =
      (body.denote (meaning.pullback select) (env.pullback select)).run handler state := by
  rw [denote_instantiate]

end Zkc.Source
