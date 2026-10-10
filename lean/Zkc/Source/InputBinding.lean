import Zkc.Source.Context

/-! Ordered input and capture binding, separate from private runtime values.

The consumer fixes the declarations. Binding checks every declared slot, even
when a branch will not read it. Names, ownership and types are checked before
constructing the total typed environment used by source and plan semantics.
-/

set_option autoImplicit false

namespace Zkc.Source

inductive InputAccess where
  | shared
  | privateTo (role : String)
  deriving DecidableEq, Repr

inductive InputKind where
  | argument
  | capture
  deriving DecidableEq, Repr

structure InputDeclaration (Ty : Type) where
  name : String
  type : Ty
  access : InputAccess
  kind : InputKind
  deriving DecidableEq, Repr

structure SuppliedInput {Ty : Type} (Value : Ty → Type) where
  name : String
  type : Ty
  value : Value type

inductive BindingError where
  | duplicateDeclaration (name : String)
  | wrongRole (name : String)
  | missingInput (name : String)
  | unexpectedInput (name : String)
  | wrongName (expected actual : String)
  | wrongType (name : String)
  deriving DecidableEq, Repr

def BindingError.code : BindingError → String
  | .duplicateDeclaration _ => "duplicate-input"
  | .wrongRole _ => "wrong-input-role"
  | .missingInput _ => "missing-input"
  | .unexpectedInput _ => "unexpected-input"
  | .wrongName _ _ => "wrong-input-name"
  | .wrongType _ => "wrong-input-type"

variable {Ty : Type} [DecidableEq Ty] {Value : Ty → Type}

private def bindOrdered (role : String) : (declarations : List (InputDeclaration Ty)) →
    List (SuppliedInput Value) → Except BindingError (Values Value (declarations.map (·.type)))
  | [], [] => .ok .nil
  | [], value :: _ => .error (.unexpectedInput value.name)
  | declaration :: _, [] => .error (.missingInput declaration.name)
  | declaration :: declarations, supplied :: values => do
    if declaration.access != .shared && declaration.access != .privateTo role then
      throw (.wrongRole declaration.name)
    if declaration.name != supplied.name then
      throw (.wrongName declaration.name supplied.name)
    if same : supplied.type = declaration.type then
      let tail ← bindOrdered role declarations values
      pure (.cons (cast (congrArg Value same) supplied.value) tail)
    else throw (.wrongType declaration.name)

private def checkNames : List (InputDeclaration Ty) → Except BindingError Unit
  | [] => .ok ()
  | declaration :: tail =>
    if tail.any (fun other => other.name == declaration.name) then
      .error (.duplicateDeclaration declaration.name)
    else checkNames tail

def bindInputs (role : String) (declarations : List (InputDeclaration Ty))
    (values : List (SuppliedInput Value)) :
    Except BindingError (Values Value (declarations.map (·.type))) := do
  checkNames declarations
  bindOrdered role declarations values

/-- Reconstruct the named, typed inputs from the actual ordered bound values.
This does not authenticate the supplier or assert an external store's contents. -/
def suppliedFromValues : (declarations : List (InputDeclaration Ty)) →
    Values Value (declarations.map (·.type)) → List (SuppliedInput Value)
  | [], .nil => []
  | declaration :: declarations, .cons value values =>
    ⟨declaration.name, declaration.type, value⟩ :: suppliedFromValues declarations values

private theorem bindOrdered_exact (role : String)
    (declarations : List (InputDeclaration Ty)) (supplied : List (SuppliedInput Value))
    (bound : Values Value (declarations.map (·.type)))
    (accepted : bindOrdered role declarations supplied = .ok bound) :
    suppliedFromValues declarations bound = supplied := by
  induction declarations generalizing supplied with
  | nil =>
    cases supplied with
    | nil => cases bound; rfl
    | cons head tail => simp [bindOrdered] at accepted
  | cons declaration declarations ih =>
    cases supplied with
    | nil => simp [bindOrdered] at accepted
    | cons head tail =>
      simp only [bindOrdered] at accepted
      split at accepted <;> try dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at accepted
      · contradiction
      split at accepted <;> try dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at accepted
      · contradiction
      split at accepted
      · rename_i same
        cases tailBound : bindOrdered role declarations tail with
        | error error => simp [tailBound] at accepted
        | ok values =>
          simp only [tailBound, Except.ok.injEq] at accepted
          subst bound
          simp only [suppliedFromValues, ih tail values tailBound, List.cons.injEq, and_true]
          cases declaration with
          | mk name ty access kind =>
            cases head with
            | mk suppliedName suppliedTy value =>
              simp only at same
              subst suppliedTy
              simp_all
      · contradiction

/-- Acceptance relates the returned heterogeneous values to every supplied
record in order, including captures that a later branch does not read. -/
theorem bindInputs_exact (role : String) (declarations : List (InputDeclaration Ty))
    (supplied : List (SuppliedInput Value)) (bound : Values Value (declarations.map (·.type)))
    (accepted : bindInputs role declarations supplied = .ok bound) :
    suppliedFromValues declarations bound = supplied := by
  unfold bindInputs at accepted
  cases names : checkNames declarations with
  | error error => simp [names, Bind.bind, Except.bind] at accepted
  | ok result =>
    simp only [names, Bind.bind, Except.bind] at accepted
    exact bindOrdered_exact role declarations supplied bound accepted

end Zkc.Source
