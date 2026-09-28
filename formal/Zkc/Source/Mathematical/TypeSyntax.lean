import Zkc.Source.Mathematical.Raw
import Zkc.Source.Mathematical.GraphAdmission

/-! Scoped type declarations before registered interpretation.

Type uses select actual earlier declarations and carry exactly the selected
number of static arguments. Domain references are bounded manifest positions.
Registry validation and normalized expansion are separate from these scope
facts; neither a name nor a manifest position supplies a domain interpretation.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.TypeSyntax

structure Use (scope : List Nat) (arity : Nat) where
  target : Nat
  declaration : Var scope target
  arguments : List (Static.Expression arity)
  argumentCount : arguments.length = target

inductive Expression (domains : Nat) (scope : List Nat) (arity : Nat) where
  | nominal (domain : Fin domains) (constructor : String) (arguments : List (Static.Expression arity))
  | product (elements : List (Use scope arity))
  | fin (count : Static.Expression arity)
  | vector (element : Use scope arity) (count : Static.Expression arity)
  | polynomial (domain : Fin domains) (variables degree : Static.Expression arity) (convention : Raw.Degree)
  | residual (domain : Fin domains) (variables degree : Static.Expression arity)

variable {scope : List Nat} {arity domains : Nat}

def Use.erase (use : Use scope arity) : Raw.TypeUse :=
  ⟨⟨use.declaration.index⟩, use.arguments.map Static.Expression.erase⟩

def Expression.erase : Expression domains scope arity → Raw.TypeExpression
  | .nominal domain constructor arguments => .nominal ⟨domain.val⟩ constructor (arguments.map Static.Expression.erase)
  | .product elements => .product (elements.map Use.erase)
  | .fin count => .fin count.erase
  | .vector element count => .vector element.erase count.erase
  | .polynomial domain variables degree convention => .polynomial ⟨domain.val⟩ variables.erase degree.erase convention
  | .residual domain variables degree => .residual ⟨domain.val⟩ variables.erase degree.erase

inductive Error where
  | resource | reference | domain | arity
  | static (reason : Static.Error)
  deriving DecidableEq, Repr

def staticArguments (arity : Nat) : (raw : List Static.Raw) →
    Except Error { arguments : List (Static.Expression arity) // arguments.map Static.Expression.erase = raw }
  | [] => return ⟨[], rfl⟩
  | first :: rest => do
      let first ← (Static.decode arity 65 first).mapError Error.static
      let rest ← staticArguments arity rest
      return ⟨first.val :: rest.val, by simp [first.property, rest.property]⟩

def use (scope : List Nat) (arity : Nat) (raw : Raw.TypeUse) :
    Except Error { value : Use scope arity // value.erase = raw } := do
  let selected ← (Graph.select scope raw.type.index).mapError (fun _ => Error.reference)
  let arguments ← staticArguments arity raw.statics
  if count : arguments.val.length = selected.ty then
    return ⟨⟨selected.ty, selected.value, arguments.val, count⟩, by
      cases raw with
      | mk type statics =>
          cases type
          simp [Use.erase, selected.erasure, arguments.property]⟩
  else throw .arity

def uses (scope : List Nat) (arity : Nat) : (raw : List Raw.TypeUse) →
    Except Error { values : List (Use scope arity) // values.map Use.erase = raw }
  | [] => return ⟨[], rfl⟩
  | first :: rest => do
      let first ← use scope arity first
      let rest ← uses scope arity rest
      return ⟨first.val :: rest.val, by simp [first.property, rest.property]⟩

private def domain (domains : Nat) (raw : Raw.Reference .domain) :
    Except Error { value : Fin domains // value.val = raw.index } :=
  if bound : raw.index < domains then .ok ⟨⟨raw.index, bound⟩, rfl⟩ else .error .domain

def decode (domains : Nat) (scope : List Nat) (arity : Nat) (raw : Raw.TypeExpression) :
    Except Error { value : Expression domains scope arity // value.erase = raw } := do
  match hraw : raw with
  | .nominal index constructor arguments =>
      let selected ← domain domains index
      let values ← staticArguments arity arguments
      return ⟨.nominal selected.val constructor values.val, by
        cases index
        simp [Expression.erase, selected.property, values.property, hraw]⟩
  | .product elements =>
      let values ← uses scope arity elements
      return ⟨.product values.val, by simp [Expression.erase, values.property, hraw]⟩
  | .fin count =>
      let value ← (Static.decode arity 65 count).mapError Error.static
      return ⟨.fin value.val, by simp [Expression.erase, value.property, hraw]⟩
  | .vector element count =>
      let element ← use scope arity element
      let count ← (Static.decode arity 65 count).mapError Error.static
      return ⟨.vector element.val count.val, by simp [Expression.erase, element.property, count.property, hraw]⟩
  | .polynomial index variables degree convention =>
      let selected ← domain domains index
      let variables ← (Static.decode arity 65 variables).mapError Error.static
      let degree ← (Static.decode arity 65 degree).mapError Error.static
      return ⟨.polynomial selected.val variables.val degree.val convention, by
        cases index
        simp [Expression.erase, selected.property, variables.property, degree.property, hraw]⟩
  | .residual index variables degree =>
      let selected ← domain domains index
      let variables ← (Static.decode arity 65 variables).mapError Error.static
      let degree ← (Static.decode arity 65 degree).mapError Error.static
      return ⟨.residual selected.val variables.val degree.val, by
        cases index
        simp [Expression.erase, selected.property, variables.property, degree.property, hraw]⟩

/-- The scope grows only after a body has been decoded. References in that
body therefore select earlier templates in their original table order. -/
inductive Templates (domains : Nat) : List Nat → Type where
  | nil : Templates domains []
  | snoc {scope : List Nat} (previous : Templates domains scope) (arity : Nat)
      (body : Expression domains scope arity) : Templates domains (scope ++ [arity])

def Templates.erase {scope} : Templates domains scope → List Raw.TypeTemplate
  | .nil => []
  | .snoc previous arity body => previous.erase ++ [⟨arity, body.erase⟩]

structure Appended {scope} (previous : Templates domains scope) (raw : List Raw.TypeTemplate) where
  arities : List Nat
  templates : Templates domains arities
  erasure : templates.erase = previous.erase ++ raw

def append {scope} (previous : Templates domains scope) :
    (raw : List Raw.TypeTemplate) → Except Error (Appended previous raw)
  | [] => return ⟨scope, previous, by simp⟩
  | first :: rest => do
      if first.statics ≥ Static.limit then throw .arity
      let body ← decode domains scope first.statics first.body
      let tail ← append (.snoc previous first.statics body.val) rest
      return ⟨tail.arities, tail.templates, by
        rw [tail.erasure]
        simp only [Templates.erase, body.property, List.append_assoc, List.singleton_append]⟩

def declarations (domains : Nat) (raw : List Raw.TypeTemplate) :=
  append (Templates.nil (domains := domains)) raw

theorem declarations_erases (domains : Nat) {raw result}
    (_accepted : declarations domains raw = .ok result) : result.templates.erase = raw :=
  result.erasure

end Zkc.Source.Mathematical.TypeSyntax
