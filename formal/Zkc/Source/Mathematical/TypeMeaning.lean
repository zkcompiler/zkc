import Zkc.Source.Mathematical.TypeSyntax

/-! Mathematical meaning of scoped type templates.

The consumer supplies registered atomic meanings. Products, finite indices and
vectors are built in. This interpretation follows the actual earlier-template
reference and evaluates the authored static argument tree; it does not identify
a domain name with a proof or physical representation.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.TypeSyntax

structure Interpretation (domains : Nat) where
  nominal : Fin domains → String → List Nat → Type
  polynomial : Fin domains → Nat → Nat → Raw.Degree → Type
  residual : Fin domains → Nat → Nat → Type

abbrev Environment (scope : List Nat) :=
  {arity : Nat} → Var scope arity → (Fin arity → Nat) → Type

variable {domains arity : Nat} {scope : List Nat}

def Use.parameters (use : Use scope arity) (values : Fin arity → Nat) : Fin use.target → Nat :=
  fun index => (use.arguments[index.val]'(by rw [use.argumentCount]; exact index.isLt)).eval values

def Use.denote (env : Environment scope) (use : Use scope arity) (values : Fin arity → Nat) : Type :=
  env use.declaration (use.parameters values)

def productTypes : List Type → Type
  | [] => PUnit
  | first :: rest => first × productTypes rest

def Expression.denote (meaning : Interpretation domains) (env : Environment scope)
    (values : Fin arity → Nat) : Expression domains scope arity → Type
  | .nominal domain constructor arguments => meaning.nominal domain constructor (arguments.map (·.eval values))
  | .product elements => productTypes (elements.map fun element => element.denote env values)
  | .fin count => Fin (count.eval values)
  | .vector element count => Fin (count.eval values) → element.denote env values
  | .polynomial domain variables degree convention =>
      meaning.polynomial domain (variables.eval values) (degree.eval values) convention
  | .residual domain variables degree => meaning.residual domain (variables.eval values) (degree.eval values)

def Environment.snoc {arity : Nat} (value : (Fin arity → Nat) → Type) :
    {scope : List Nat} → Environment scope → Environment (scope ++ [arity])
  | [], _, _, .here => value
  | _ :: _, env, _, .here => env .here
  | _ :: _, env, _, .there ref => Environment.snoc value (fun v => env (.there v)) ref

def Templates.denote (meaning : Interpretation domains) {scope} : Templates domains scope → Environment scope
  | .nil => fun ref => nomatch ref
  | .snoc previous _ body =>
      let earlier : Environment _ := previous.denote meaning
      Environment.snoc (fun values => body.denote meaning earlier values) earlier

variable {target : Nat}

def Use.substitute (use : Use scope arity) (parameters : Fin arity → Static.Expression target) :
    Use scope target :=
  ⟨use.target, use.declaration, use.arguments.map (·.substitute parameters), by simp [use.argumentCount]⟩

theorem Use.parameters_substitute (use : Use scope arity)
    (parameters : Fin arity → Static.Expression target) (values : Fin target → Nat) :
    (use.substitute parameters).parameters values =
      use.parameters (fun index => (parameters index).eval values) := by
  funext index
  simp [Use.parameters, Use.substitute, Static.Expression.eval_substitute]

theorem Use.denote_substitute (env : Environment scope) (use : Use scope arity)
    (parameters : Fin arity → Static.Expression target) (values : Fin target → Nat) :
    (use.substitute parameters).denote env values =
      use.denote env (fun index => (parameters index).eval values) := by
  unfold Use.denote
  rw [Use.parameters_substitute]
  rfl

def Expression.substitute (parameters : Fin arity → Static.Expression target) :
    Expression domains scope arity → Expression domains scope target
  | .nominal domain constructor arguments => .nominal domain constructor (arguments.map (·.substitute parameters))
  | .product elements => .product (elements.map (·.substitute parameters))
  | .fin count => .fin (count.substitute parameters)
  | .vector element count => .vector (element.substitute parameters) (count.substitute parameters)
  | .polynomial domain variables degree convention =>
      .polynomial domain (variables.substitute parameters) (degree.substitute parameters) convention
  | .residual domain variables degree => .residual domain (variables.substitute parameters) (degree.substitute parameters)

/-- Substitution commutes with the actual earlier-template and registered type
meanings. Normalization can be justified separately by its static certificate. -/
theorem Expression.denote_substitute (meaning : Interpretation domains) (env : Environment scope)
    (expression : Expression domains scope arity)
    (parameters : Fin arity → Static.Expression target) (values : Fin target → Nat) :
    (expression.substitute parameters).denote meaning env values =
      expression.denote meaning env (fun index => (parameters index).eval values) := by
  cases expression <;>
    simp [Expression.substitute, Expression.denote, List.map_map, Function.comp_def,
      Use.denote_substitute, Static.Expression.eval_substitute]

end Zkc.Source.Mathematical.TypeSyntax
