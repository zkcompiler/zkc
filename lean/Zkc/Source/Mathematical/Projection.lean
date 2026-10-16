module

public import Zkc.Source.Mathematical
public import Zkc.Source.ScalarRegion
public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! Mathematical reference blocks as canonical typed local regions.

Projection keeps optional components explicit and introduces no execution effect.
The generated region uses only return, operation binding and nested binding, with
explicit singleton results. The interpretation accepts an explicit condition
policy for compatibility with the enclosing region
language; this policy is never inspected by a projected mathematical block.

This connects two independent Lean models. It neither invokes the native compiler
nor gives a complete distributed projection or a communication/security theorem.
-/

set_option autoImplicit false

namespace Zkc.Source.Mathematical

/-- Additional descriptors express component selection without a communication action. -/
inductive ProjectedOp (language : Language) where
  | mathematical (op : language.Op)
  | restrict (sort : language.Ty) (selected : Bool)

/-- Reference operation vocabulary used by the canonical scalar dialect. -/
def projectedLanguage (language : Language) : Language where
  Ty := language.Ty
  Op := ProjectedOp language
  arguments
    | .mathematical op => language.arguments op
    | .restrict sort _ => [sort]
  result
    | .mathematical op => language.result op
    | .restrict sort _ => sort
  condition := language.condition

variable {Role : Type} {language : Language} {interface : PIR.Signature}

/-- No defaults are invented for absent components. Branch behavior, if used by
an enclosing region, belongs to its separately supplied condition policy. -/
def Meaning.projected (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool) :
    RegionMeaning (scalarDialect (projectedLanguage language)) interface :=
  Interpretation.regionMeaning {
    Value := fun sort => Option (meaning.Value sort)
    condition := condition
    operation
      | .mathematical op, args => .done ((RoleFamily.sequence args).map (meaning.operation op))
      | .restrict _ selected, .cons value .nil => .done (if selected then value else none)
  }

/-- Project an independent mathematical block into the canonical region carrier. -/
def Block.project (role : Role) {Γ ty} :
    Block Role language Γ ty → Region (scalarDialect (projectedLanguage language)) Γ [ty]
  | .ret value => .ret (Values.singleton value)
  | .letOp op args next => .letOp (.ordinary (.mathematical op)) args .nil (next.project role)
  | .restrict (selected := sort) scope value next =>
      .letOp (.ordinary (.restrict sort (scope role))) (.cons value .nil) .nil (next.project role)
  | .bind body next => .bind (body.project role) (next.project role)

/-- The actual generated region returns the independent component evaluator's
result for every interpretation and input, without calling any external handler. -/
theorem Block.denote_project (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool)
    (role : Role) {Γ ty} (block : Block Role language Γ ty)
    (env : Environment (fun sort => Option (meaning.Value sort)) Γ) :
    (block.project role).denote (meaning.projected (interface := interface) condition) env =
      .done (Values.singleton (block.evalAt meaning role env)) := by
  induction block with
  | ret value => rfl
  | letOp op args next ih =>
      exact ih _
  | restrict scope value next ih =>
      exact ih _
  | bind body next bodyIH nextIH =>
      simp only [project, Region.denote, bodyIH, PIR.Proc.bind, evalAt]
      exact nextIH _

/-- Complete deterministic execution preserves state and emits no events. -/
theorem Block.run_project (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool)
    (role : Role) {Γ ty} (block : Block Role language Γ ty)
    (env : Environment (fun sort => RoleFamily.Family Role (meaning.Value sort)) Γ)
    {S E : Type} (handler : PIR.Handler interface S E) (state : S) :
    ((block.project role).denote (meaning.projected condition)
      (RoleFamily.project env role)).run handler state =
        ⟨.returned (Values.singleton (block.eval meaning env role)), state, []⟩ := by
  rw [denote_project, ← eval_project]
  rfl

/-- An arbitrary open continuation sees the same component, including when it
later receives dishonest replies, emits events or stops. -/
theorem Block.continue_project (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool)
    (role : Role) {Γ ty} (block : Block Role language Γ ty)
    (env : Environment (fun sort => RoleFamily.Family Role (meaning.Value sort)) Γ)
    {A : Type}
    (next : Values (fun sort => Option (meaning.Value sort)) [ty] → PIR.Proc interface A) :
    ((block.project role).denote (meaning.projected condition)
      (RoleFamily.project env role)).bind next =
        next (Values.singleton (block.eval meaning env role)) := by
  rw [denote_project, ← eval_project]
  rfl

/-- A reference continuation can explicitly extract the sole canonical result. -/
theorem Block.continue_project_scalar (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool)
    (role : Role) {Γ ty} (block : Block Role language Γ ty)
    (env : Environment (fun sort => RoleFamily.Family Role (meaning.Value sort)) Γ)
    {A : Type} (next : Option (meaning.Value ty) → PIR.Proc interface A) :
    ((block.project role).denote (meaning.projected condition)
      (RoleFamily.project env role)).bind (fun values => next (values.get .here)) =
        next (block.eval meaning env role) := by
  exact block.continue_project meaning condition role env (fun values => next (values.get .here))

/-- Reading availability from the projected singleton recovers the reference
scope exactly when the input family matches its declared scopes. -/
theorem Block.available_project (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool)
    (role : Role) {Γ ty} (block : Block Role language Γ ty)
    (env : Environment (fun sort => RoleFamily.Family Role (meaning.Value sort)) Γ)
    (scopes : Environment (fun _ => Role → Bool) Γ) (bound : Matches meaning env scopes) :
    ((block.project role).denote (meaning.projected (interface := interface) condition)
      (RoleFamily.project env role)).bind (fun values => .done (values.get .here).isSome) =
        .done (block.scope scopes role) := by
  exact (block.continue_project_scalar meaning condition role env
    (fun value => .done value.isSome)).trans
      (congrArg PIR.Proc.done (block.eval_available meaning env scopes bound role))

/-- The same connection holds for a probabilistic or other monadic handler.
No distributional premise, independence claim or security reduction is added. -/
theorem Block.runM_project {m : Type → Type} [Monad m]
    (meaning : Meaning language)
    (condition : Option (meaning.Value language.condition) → Bool)
    (role : Role) {Γ ty} (block : Block Role language Γ ty)
    (env : Environment (fun sort => RoleFamily.Family Role (meaning.Value sort)) Γ)
    {S E : Type} (handler : PIR.MonadHandler m interface S E) (state : S) :
    ((block.project role).denote (meaning.projected condition)
      (RoleFamily.project env role)).runM handler state =
        pure ⟨.returned (Values.singleton (block.eval meaning env role)), state, []⟩ := by
  rw [denote_project, ← eval_project]
  rfl

end Zkc.Source.Mathematical
