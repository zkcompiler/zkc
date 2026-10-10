import Zkc.Source.Region

/-! Multi-result operation signatures embedded in the existing typed region.

A bundle is an ordered heterogeneous list. Empty bundles represent unit;
singleton bundles represent individual SSA values. Each primitive executes once.
Packing and projection are pure administrative operations, with no handler calls,
allocation claims or cryptographic interpretation of their own.
-/

set_option autoImplicit false

namespace Zkc.Source.ResultBundle

structure Signature where
  Ty : Type
  Op : Type
  arguments : Op → List Ty
  results : Op → List Ty
  condition : Ty

variable {signature : Signature}

inductive Operation (signature : Signature) where
  | invoke (op : signature.Op)
  | pack (types : List signature.Ty)
  | project {types : List signature.Ty} {ty : signature.Ty} (member : Var types ty)

abbrev language (signature : Signature) : Language where
  Ty := List signature.Ty
  Op := Operation signature
  arguments
    | .invoke op => (signature.arguments op).map List.singleton
    | .pack types => types.map List.singleton
    | .project (types := types) _ => [types]
  result
    | .invoke op => signature.results op
    | .pack types => types
    | .project (ty := ty) _ => [ty]
  condition := [signature.condition]

variable {Ty : Type} {Value : Ty → Type}

/-- Split an ordered result bundle into the values bound to individual ports. -/
def singletons {types : List Ty} :
    Values Value types → Values (Values Value) (types.map List.singleton)
  | .nil => .nil
  | .cons value rest => .cons (.cons value .nil) (singletons rest)

def join : {types : List Ty} →
    Values (Values Value) (types.map List.singleton) → Values Value types
  | [], .nil => .nil
  | _ :: _, .cons (.cons value .nil) rest => .cons value (join rest)

@[simp] theorem join_singletons {types : List Ty} (values : Values Value types) :
    join (singletons values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => exact congrArg (Values.cons value) ih

structure Meaning (signature : Signature) (interface : PIR.Signature) where
  Value : signature.Ty → Type
  condition : Value signature.condition → Bool
  operation : (op : signature.Op) → Values Value (signature.arguments op) →
    PIR.Proc interface (Values Value (signature.results op))

variable {interface : PIR.Signature}

abbrev Meaning.interpretation (meaning : Meaning signature interface) :
    Interpretation (language signature) interface where
  Value := Values meaning.Value
  condition values := match values with
    | .cons value .nil => meaning.condition value
  operation
    | .invoke op, args => meaning.operation op (join args)
    | .pack _, args => .done (join args)
    | .project member, .cons bundle .nil => .done (.cons (bundle.get member) .nil)

/-- Enumerate a context's members in declaration order, including repeated types. -/
def members (types : List Ty) : Operands types types :=
  match types with
  | [] => .nil
  | _ :: rest => .cons .here (Operands.rename (fun v => .there v) (members rest))

@[simp] theorem eval_members {types : List Ty} (values : Values Value types) :
    (members types).eval values.get = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [members, Operands.eval, Values.get, Operands.eval_rename]
      exact congrArg (Values.cons value) ih

/-- Project a bundle into separate SSA bindings, preserving declared result order.
The continuation keeps the surrounding context, including the original bundle.
Formation/affinity checks remain a separate obligation of a source elaborator. -/
def unpack {Γ : List (List signature.Ty)} {types result : List signature.Ty}
    (bundle : Var Γ types) : {outputs : List signature.Ty} →
    Operands types outputs →
    Region (language signature) (outputs.map List.singleton ++ Γ) result →
    Region (language signature) Γ result
  | [], .nil, next => next
  | _ :: _, .cons member rest, next =>
      unpack bundle rest (.letOp (.project member)
        (.cons (bundle.weakenPrefix _) .nil) next)

theorem denote_unpack (meaning : Meaning signature interface)
    {Γ : List (List signature.Ty)} {types result outputs : List signature.Ty}
    (bundle : Var Γ types) (projections : Operands types outputs)
    (next : Region (language signature) (outputs.map List.singleton ++ Γ) result)
    (env : Environment (Values meaning.Value) Γ) :
    (unpack bundle projections next).denote meaning.interpretation env =
      next.denote meaning.interpretation
        (env.prepend (singletons (projections.eval (env bundle).get))) := by
  induction projections with
  | nil => rfl
  | cons member rest ih =>
      simp only [unpack, ih, Region.denote, Meaning.interpretation,
        Operands.eval, Environment.prepend_weakenPrefix, PIR.Proc.bind,
        singletons, Environment.prepend]
      rfl

/-- Invoke once and bind all results using the existing region carrier. A
zero-result operation still executes and can stop before its continuation. -/
def invoke {Γ : List (List signature.Ty)} {result : List signature.Ty}
    (op : signature.Op) (arguments : Operands Γ ((signature.arguments op).map List.singleton))
    (next : Region (language signature)
      ((signature.results op).map List.singleton ++ signature.results op :: Γ) result) :
    Region (language signature) Γ result :=
  .letOp (.invoke op) arguments (unpack .here (members _) next)

theorem denote_invoke (meaning : Meaning signature interface)
    {Γ : List (List signature.Ty)} {result : List signature.Ty}
    (op : signature.Op) (arguments : Operands Γ ((signature.arguments op).map List.singleton))
    (next : Region (language signature)
      ((signature.results op).map List.singleton ++ signature.results op :: Γ) result)
    (env : Environment (Values meaning.Value) Γ) :
    (invoke op arguments next).denote meaning.interpretation env =
      (meaning.operation op (join (arguments.eval env))).bind fun results =>
        next.denote meaning.interpretation
          (Environment.prepend (env.push results) (singletons results)) := by
  simp only [invoke, Region.denote, Meaning.interpretation]
  congr 1
  funext results
  rw [denote_unpack]
  simp only [Environment.push, eval_members]

/-- Equality includes any stopped post-state and event prefix. The adapter does
not retry, split or roll back a primitive that consumed authority before stopping. -/
theorem run_invoke (meaning : Meaning signature interface)
    {S E : Type} (handler : PIR.Handler interface S E)
    {Γ : List (List signature.Ty)} {result : List signature.Ty}
    (op : signature.Op) (arguments : Operands Γ ((signature.arguments op).map List.singleton))
    (next : Region (language signature)
      ((signature.results op).map List.singleton ++ signature.results op :: Γ) result)
    (env : Environment (Values meaning.Value) Γ) (state : S) :
    ((invoke op arguments next).denote meaning.interpretation env).run handler state =
      ((meaning.operation op (join (arguments.eval env))).run handler state).follow
        (fun results => (next.denote meaning.interpretation
          (Environment.prepend (env.push results) (singletons results))).run handler) := by
  rw [denote_invoke, PIR.run_bind]

end Zkc.Source.ResultBundle
