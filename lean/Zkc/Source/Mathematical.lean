module

public import Zkc.Source.RoleFamily
public import Zkc.Source.Program

@[expose] public section

/-! Mathematical SSA blocks with role-indexed values.

The grammar retains typed, ordered references and explicit role restrictions.
Operations have a total mathematical interpretation; ordered local algorithms
and protocol actions use the existing effectful source and `PIR.Process` models.
This independent source profile is not a native parser or projection theorem.
-/

set_option autoImplicit false

namespace Zkc.Source.Mathematical

open RoleFamily (Family)

/-- Pure domain meanings are separate from operations that can stop or emit events. -/
structure Meaning (language : Language) where
  Value : language.Ty → Type
  operation : (op : language.Op) → Values Value (language.arguments op) →
    Value (language.result op)

/-- A total block has shared SSA bindings and no host-language continuations. -/
inductive Block (Role : Type) (language : Language) :
    List language.Ty → language.Ty → Type where
  | ret {Γ ty} (value : Var Γ ty) : Block Role language Γ ty
  | letOp {Γ ty} (op : language.Op) (args : Operands Γ (language.arguments op))
      (next : Block Role language (language.result op :: Γ) ty) : Block Role language Γ ty
  | restrict {Γ ty selected} (scope : Role → Bool) (value : Var Γ selected)
      (next : Block Role language (selected :: Γ) ty) : Block Role language Γ ty
  | bind {Γ ty result} (body : Block Role language Γ result)
      (next : Block Role language (result :: Γ) ty) : Block Role language Γ ty

variable {Role : Type} {language : Language}

/-- Evaluate all components pointwise. Admission is a separate predicate below. -/
def Block.eval (meaning : Meaning language) {Γ ty} :
    Block Role language Γ ty →
      Environment (fun sort => Family Role (meaning.Value sort)) Γ →
        Family Role (meaning.Value ty)
  | .ret value, env => env value
  | .letOp op args next, env =>
      next.eval meaning (env.push (RoleFamily.apply (meaning.operation op) (args.eval env)))
  | .restrict scope value next, env =>
      next.eval meaning (env.push (RoleFamily.restrict scope (env value)))
  | .bind body next, env => next.eval meaning (env.push (body.eval meaning env))

/-- An independent component evaluator has only one role's inputs. A missing
component remains absent; foreign-only mathematical work does not stop this role. -/
def Block.evalAt (meaning : Meaning language) (role : Role) {Γ ty} :
    Block Role language Γ ty →
      Environment (fun sort => Option (meaning.Value sort)) Γ → Option (meaning.Value ty)
  | .ret value, env => env value
  | .letOp op args next, env =>
      next.evalAt meaning role
        (env.push ((RoleFamily.sequence (args.eval env)).map (meaning.operation op)))
  | .restrict scope value next, env =>
      next.evalAt meaning role (env.push (if scope role then env value else none))
  | .bind body next, env => next.evalAt meaning role (env.push (body.evalAt meaning role env))

/-- Selecting a component commutes with evaluating the mathematical block.
The result covers every input family, including disagreeing role components. -/
theorem Block.eval_project (meaning : Meaning language) {Γ ty}
    (block : Block Role language Γ ty)
    (env : Environment (fun sort => Family Role (meaning.Value sort)) Γ) (role : Role) :
    block.eval meaning env role = block.evalAt meaning role (RoleFamily.project env role) := by
  induction block with
  | ret value => rfl
  | letOp op args next ih =>
      simp only [eval, evalAt, ih, RoleFamily.project_push, RoleFamily.apply,
        RoleFamily.read_operands]
  | restrict scope value next ih =>
      simp only [eval, evalAt, ih, RoleFamily.project_push, RoleFamily.restrict,
        RoleFamily.project]
  | bind body next bodyIH nextIH =>
      simp only [eval, evalAt, nextIH, RoleFamily.project_push, bodyIH]

/-- A role cannot distinguish changes to components absent from its input view. -/
theorem Block.eval_local (meaning : Meaning language) {Γ ty}
    (block : Block Role language Γ ty)
    (first second : Environment (fun sort => Family Role (meaning.Value sort)) Γ)
    (role : Role) (same : @Eq (Environment (fun sort => Option (meaning.Value sort)) Γ)
      (RoleFamily.project first role) (RoleFamily.project second role)) :
    block.eval meaning first role = block.eval meaning second role := by
  rw [eval_project, eval_project, same]

/-- Static scope inference uses all ordered operands, independently of their values. -/
def operandScope {Γ : List language.Ty}
    (scopes : Environment (fun _ => Role → Bool) Γ) :
    {types : List language.Ty} → Operands Γ types → Role → Bool
  | [], .nil, _ => true
  | _ :: _, .cons value rest, role => scopes value role && operandScope scopes rest role

/-- Infer the returned scope. Admission separately checks every intermediate binding. -/
def Block.scope {Γ ty} : Block Role language Γ ty →
    Environment (fun _ => Role → Bool) Γ → Role → Bool
  | .ret value, scopes => scopes value
  | .letOp _ args next, scopes => next.scope (scopes.push (operandScope scopes args))
  | .restrict selected value next, scopes =>
      next.scope (scopes.push (fun role => selected role && scopes value role))
  | .bind body next, scopes => next.scope (scopes.push (body.scope scopes))

/-- Every definition must have a nonempty scope, including unused definitions.
A restriction must select a nonempty subset of the original scope. This predicate
depends on syntax and input scopes, not on mathematical values or runtime guards. -/
def Block.Admitted {Γ ty} : Block Role language Γ ty →
    Environment (fun _ => Role → Bool) Γ → Prop
  | .ret value, scopes => ∃ role, scopes value role = true
  | .letOp _ args next, scopes =>
      (∃ role, operandScope scopes args role = true) ∧
        next.Admitted (scopes.push (operandScope scopes args))
  | .restrict selected value next, scopes =>
      (∃ role, selected role = true) ∧
      (∀ role, selected role = true → scopes value role = true) ∧
        next.Admitted (scopes.push (fun role => selected role && scopes value role))
  | .bind body next, scopes =>
      body.Admitted scopes ∧ next.Admitted (scopes.push (body.scope scopes))

/-- Actual input binding must provide exactly the advertised components. -/
def Matches (meaning : Meaning language) {Γ : List language.Ty}
    (env : Environment (fun sort => Family Role (meaning.Value sort)) Γ)
    (scopes : Environment (fun _ => Role → Bool) Γ) : Prop :=
  ∀ {sort} (ref : Var Γ sort) role, RoleFamily.available (env ref) role = scopes ref role

theorem operand_available (meaning : Meaning language) {Γ types : List language.Ty}
    (args : Operands Γ types)
    (env : Environment (fun sort => Family Role (meaning.Value sort)) Γ)
    (scopes : Environment (fun _ => Role → Bool) Γ) (bound : Matches meaning env scopes)
    (role : Role) :
    RoleFamily.allAvailable role (args.eval env) = operandScope scopes args role := by
  induction args with
  | nil => rfl
  | cons value rest ih =>
      simp only [Operands.eval, RoleFamily.allAvailable, operandScope, bound value role, ih]

/-- Scope inference is exact for every total interpretation and correctly bound
input family. It does not identify distinct components with a shared public value. -/
theorem Block.eval_available (meaning : Meaning language) {Γ ty}
    (block : Block Role language Γ ty)
    (env : Environment (fun sort => Family Role (meaning.Value sort)) Γ)
    (scopes : Environment (fun _ => Role → Bool) Γ) (bound : Matches meaning env scopes)
    (role : Role) :
    RoleFamily.available (block.eval meaning env) role = block.scope scopes role := by
  induction block generalizing role with
  | ret value => exact bound value role
  | letOp op args next ih =>
      apply ih
      intro sort ref actor
      cases ref with
      | here => exact (RoleFamily.apply_available _ _ _).trans (operand_available meaning args env scopes bound actor)
      | there ref => exact bound ref actor
  | restrict selected value next ih =>
      apply ih
      intro sort ref actor
      cases ref with
      | here =>
          change RoleFamily.available (RoleFamily.restrict selected (env value)) actor = _
          rw [RoleFamily.available_restrict, bound]
          rfl
      | there ref => exact bound ref actor
  | bind body next bodyIH nextIH =>
      apply nextIH
      intro sort ref actor
      cases ref with
      | here => exact bodyIH env scopes bound actor
      | there ref => exact bound ref actor

/-- Executable scope admission for a selected finite role roster. The soundness
theorem requires this roster to cover the model's role type. -/
def Block.check (roles : List Role) {Γ ty} : Block Role language Γ ty →
    Environment (fun _ => Role → Bool) Γ → Bool
  | .ret value, scopes => roles.any (scopes value)
  | .letOp _ args next, scopes =>
      roles.any (operandScope scopes args) && next.check roles (scopes.push (operandScope scopes args))
  | .restrict selected value next, scopes =>
      roles.any selected &&
        roles.all (fun role => decide (selected role = true → scopes value role = true)) &&
        next.check roles (scopes.push (fun role => selected role && scopes value role))
  | .bind body next, scopes =>
      body.check roles scopes && next.check roles (scopes.push (body.scope scopes))

private theorem any_roles (roles : List Role) (covers : ∀ role, role ∈ roles)
    (predicate : Role → Bool) : roles.any predicate = true ↔ ∃ role, predicate role = true := by
  simp [List.any_eq_true, covers]

private theorem all_roles (roles : List Role) (covers : ∀ role, role ∈ roles)
    (predicate : Role → Bool) : roles.all predicate = true ↔ ∀ role, predicate role = true := by
  simp [List.all_eq_true, covers]

/-- The finite checker admits exactly the declared scope predicate. Admission
does not check algebraic identities, probabilities or native byte decoding. -/
theorem Block.check_iff (roles : List Role) (covers : ∀ role, role ∈ roles) {Γ ty}
    (block : Block Role language Γ ty) (scopes : Environment (fun _ => Role → Bool) Γ) :
    block.check roles scopes = true ↔ block.Admitted scopes := by
  induction block with
  | ret value => exact any_roles roles covers _
  | letOp op args next ih =>
      simp only [check, Admitted, Bool.and_eq_true, any_roles roles covers, ih]
  | restrict selected value next ih =>
      simp only [check, Admitted, Bool.and_eq_true, any_roles roles covers,
        all_roles roles covers, decide_eq_true_eq, ih, and_assoc]
  | bind body next bodyIH nextIH =>
      simp only [check, Admitted, Bool.and_eq_true, bodyIH, nextIH]

/-- A formed block returns at least one component at the mathematical boundary. -/
theorem Block.admitted_scope {Γ ty} (block : Block Role language Γ ty)
    (scopes : Environment (fun _ => Role → Bool) Γ) (admitted : block.Admitted scopes) :
    ∃ role, block.scope scopes role = true := by
  induction block with
  | ret value => exact admitted
  | letOp op args next ih => exact ih _ admitted.2
  | restrict selected value next ih => exact ih _ admitted.2.2
  | bind body next bodyIH nextIH => exact nextIH _ admitted.2

/-- Explicit references make renaming preserve every original dependency. -/
def Block.rename {Γ Δ ty} (rename : Renaming Γ Δ) :
    Block Role language Γ ty → Block Role language Δ ty
  | .ret value => .ret (rename value)
  | .letOp op args next => .letOp op (args.rename rename) (next.rename rename.lift)
  | .restrict scope value next => .restrict scope (rename value) (next.rename rename.lift)
  | .bind body next => .bind (body.rename rename) (next.rename rename.lift)

theorem Block.eval_rename (meaning : Meaning language) {Γ Δ ty}
    (block : Block Role language Γ ty) (rename : Renaming Γ Δ)
    (env : Environment (fun sort => Family Role (meaning.Value sort)) Δ) :
    (block.rename rename).eval meaning env = block.eval meaning (fun ref => env (rename ref)) := by
  induction block generalizing Δ with
  | ret value => rfl
  | letOp op args next ih =>
      simp only [Block.rename, eval, Operands.eval_rename]
      rw [ih, Environment.push_rename]
  | restrict scope value next ih =>
      simp only [Block.rename, eval]
      rw [ih, Environment.push_rename]
  | bind body next bodyIH nextIH =>
      simp only [Block.rename, eval, bodyIH]
      rw [nextIH, Environment.push_rename]

end Zkc.Source.Mathematical
