import Zkc.Source.Region

/-! Shared, typed definitions for structured source.

References select a stored body and its exact argument/result signature. Each
body can call only earlier definitions, giving an acyclic module without fuel
or host-language implementation callbacks. Definition sharing is syntactic;
the denotation uses the existing complete `PIR.Proc` execution semantics.

This is the resolved call layer. Symbol-name resolution, protocol role admission,
instance selection and participant projection remain separate obligations.
-/

set_option autoImplicit false

namespace Zkc.Source

structure DefinitionSignature (Ty : Type) where
  arguments : List Ty
  result : Ty
  deriving DecidableEq, Repr

/-- Primitive operations and references to actual in-scope definitions. -/
inductive DefinitionOp (language : Language)
    (scope : List (DefinitionSignature language.Ty)) where
  | primitive (op : language.Op)
  | call {signature : DefinitionSignature language.Ty} (callee : Var scope signature)

abbrev Language.withDefinitions (language : Language)
    (scope : List (DefinitionSignature language.Ty)) : Language where
  Ty := language.Ty
  Op := DefinitionOp language scope
  arguments
    | .primitive op => language.arguments op
    | .call (signature := signature) _ => signature.arguments
  result
    | .primitive op => language.result op
    | .call (signature := signature) _ => signature.result
  condition := language.condition

/-- A body sees its explicit parameters and earlier definitions only.
The head reference is the most recently added definition. -/
inductive Definitions (language : Language) : List (DefinitionSignature language.Ty) → Type where
  | nil : Definitions language []
  | snoc {scope : List (DefinitionSignature language.Ty)}
      (previous : Definitions language scope) (signature : DefinitionSignature language.Ty)
      (body : Region (language.withDefinitions scope) signature.arguments signature.result) :
      Definitions language (signature :: scope)

variable {language : Language} {interface : PIR.Signature}

/-- Resolve calls to stored source bodies, under the same selected primitive meaning.
Calls receive values for declared arguments, never the caller's whole environment. -/
def Definitions.operation (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)}
    (definitions : Definitions language scope) (op : DefinitionOp language scope)
    (args : Values base.Value ((language.withDefinitions scope).arguments op)) :
    PIR.Proc interface (base.Value ((language.withDefinitions scope).result op)) :=
  match definitions, op with
  | .nil, .primitive op => base.operation op args
  | .nil, .call ref => nomatch ref
  | .snoc _ _ _, .primitive op => base.operation op args
  | .snoc previous _ body, .call .here =>
      body.denote (language := language.withDefinitions _)
        { Value := base.Value, condition := base.condition, operation := previous.operation base }
        args.get
  | .snoc previous _ _, .call (.there ref) => previous.operation base (.call ref) args

abbrev Definitions.meaning (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)}
    (definitions : Definitions language scope) :
    Interpretation (language.withDefinitions scope) interface where
  Value := base.Value
  condition := base.condition
  operation := definitions.operation base

/-- Embed an existing source region without changing its primitive operations. -/
def Region.withDefinitions {Γ : List language.Ty} {ty : language.Ty}
    (scope : List (DefinitionSignature language.Ty)) :
    Region language Γ ty → Region (language.withDefinitions scope) Γ ty
  | .ret value => .ret value
  | .stop reason => .stop reason
  | .letOp op args next => .letOp (.primitive op) args (next.withDefinitions scope)
  | .branch condition yes no =>
      .branch condition (yes.withDefinitions scope) (no.withDefinitions scope)
  | .iterate count initial body next =>
      .iterate count initial (body.withDefinitions scope) (next.withDefinitions scope)
  | .bind body next => .bind (body.withDefinitions scope) (next.withDefinitions scope)

@[simp] theorem Definitions.operation_primitive (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    (op : language.Op) (args : Values base.Value (language.arguments op)) :
    definitions.operation base (.primitive op) args = base.operation op args := by
  cases definitions <;> rfl

theorem Region.denote_withDefinitions (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    {Γ : List language.Ty} {ty : language.Ty} (body : Region language Γ ty)
    (env : Environment base.Value Γ) :
    (body.withDefinitions scope).denote (definitions.meaning base) env = body.denote base env := by
  induction body with
  | ret value => rfl
  | stop reason => rfl
  | letOp op args next ih =>
      simp only [withDefinitions, denote, Definitions.meaning, Definitions.operation_primitive]
      congr 1
      funext value
      exact ih (env.push value)
  | branch condition yes no yesIH noIH =>
      simp only [withDefinitions, denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
      simp only [withDefinitions, denote]
      have same :
          (fun value => (body.withDefinitions scope).denote
            (definitions.meaning base) (env.push value)) =
          (fun value => body.denote base (env.push value)) := by
        funext value
        exact bodyIH (env.push value)
      rw [same]
      congr 1
      funext value
      exact nextIH (env.push value)
  | bind body next bodyIH nextIH =>
      simp only [withDefinitions, denote, bodyIH]
      congr 1
      funext value
      exact nextIH (env.push value)

/-- Invoke the newest actual body, with explicit argument capture and one normal suffix. -/
theorem Definitions.run_call (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (previous : Definitions language scope)
    (signature : DefinitionSignature language.Ty)
    (body : Region (language.withDefinitions scope) signature.arguments signature.result)
    {Γ : List language.Ty} {ty : language.Ty} (args : Operands Γ signature.arguments)
    (next : Region (language.withDefinitions (signature :: scope)) (signature.result :: Γ) ty)
    {S E : Type} (handler : PIR.Handler interface S E)
    (env : Environment base.Value Γ) (state : S) :
    ((Region.letOp (language := language.withDefinitions (signature :: scope))
      (.call .here) args next).denote
        ((previous.snoc signature body).meaning base) env).run handler state =
      ((body.denote (previous.meaning base) (Operands.eval env args).get).run handler state).follow
        (fun value => (next.denote ((previous.snoc signature body).meaning base)
          (env.push value)).run handler) := by
  exact PIR.run_bind _ _ _ _

/-- A stopped invocation retains the callee's post-state/events and does not run the suffix. -/
theorem Definitions.run_call_stopped (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (previous : Definitions language scope)
    (signature : DefinitionSignature language.Ty)
    (body : Region (language.withDefinitions scope) signature.arguments signature.result)
    {Γ : List language.Ty} {ty : language.Ty} (args : Operands Γ signature.arguments)
    (next : Region (language.withDefinitions (signature :: scope)) (signature.result :: Γ) ty)
    {S E : Type} (handler : PIR.Handler interface S E)
    (env : Environment base.Value Γ) (state final : S) (events : List E) (reason : PIR.Stop)
    (stopped :
      (body.denote (previous.meaning base) (Operands.eval env args).get).run handler state =
      ⟨.stopped reason, final, events⟩) :
    ((Region.letOp (language := language.withDefinitions (signature :: scope))
      (.call .here) args next).denote
      ((previous.snoc signature body).meaning base) env).run handler state =
      ⟨.stopped reason, final, events⟩ := by
  rw [run_call, stopped]
  rfl

end Zkc.Source
