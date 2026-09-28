import Zkc.Source.Mathematical.TypeMeaning
import Zkc.Source.Mathematical.StaticNormalization
import Zkc.Source.Mathematical.DataBounds

/-! Certified expansion of earlier type templates.

One stateful allowance covers template traversal and static normalization.
The result is a structural mathematical type together with its equality to
the selected template's meaning for every assignment. Domain admission is an
explicit consumer input; the meaning still comes from the selected registry.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.TypeExpansion
open TypeSyntax

inductive Atom (domains arity : Nat) where
  | nominal (domain : Fin domains) (constructor : String) (arguments : List (Static.Expression arity))
  | polynomial (domain : Fin domains) (variables degree : Static.Expression arity) (convention : Raw.Degree)
  | residual (domain : Fin domains) (variables degree : Static.Expression arity)
  deriving DecidableEq

abbrev Shape (domains arity : Nat) := Data.Shape (Atom domains arity) (Static.Expression arity)

def Atom.denote {domains arity} (meaning : TypeSyntax.Interpretation domains) (values : Fin arity → Nat) :
    Atom domains arity → Type
  | .nominal domain constructor arguments => meaning.nominal domain constructor (arguments.map (·.eval values))
  | .polynomial domain variables degree convention =>
      meaning.polynomial domain (variables.eval values) (degree.eval values) convention
  | .residual domain variables degree => meaning.residual domain (variables.eval values) (degree.eval values)

def denote {domains arity} (meaning : TypeSyntax.Interpretation domains) (shape : Shape domains arity)
    (values : Fin arity → Nat) : Type :=
  shape.Value (Atom.denote meaning values) (Static.Expression.eval values)

abbrev DomainCheck (domains : Nat) := {arity : Nat} → Atom domains arity → Bool

/-- Every domain-owned leaf was admitted by this exact consumer. Product and
vector formation preserve the evidence for their components. This predicate
says nothing about algebraic laws beyond the selected registry check. -/
inductive Formed {domains arity} (check : Atom domains arity → Bool) : Shape domains arity → Prop where
  | atom (value : Atom domains arity) (registered : check value = true) : @Formed domains arity check (.atom value)
  | product {elements : List (Shape domains arity)}
      (components : ∀ element ∈ elements, @Formed domains arity check element) : @Formed domains arity check (.product elements)
  | fin (count : Static.Expression arity) : @Formed domains arity check (.fin count)
  | vector {element : Shape domains arity} (formed : @Formed domains arity check element)
      (count : Static.Expression arity) : @Formed domains arity check (.vector element count)

structure Expanded {domains arity} (meaning : TypeSyntax.Interpretation domains)
    (check : DomainCheck domains) (source : (Fin arity → Nat) → Type) where
  shape : Shape domains arity
  sound : ∀ values, denote meaning shape values = source values
  formed : Formed check shape
  measured : Data.capacity.Measured shape

inductive Error where
  | resource | domain
  | static (reason : Static.NormalizationError)
  deriving DecidableEq, Repr

abbrev Admission := StateT Nat (Except Error)

def consume (amount : Nat := 1) : Admission Unit := do
  let available ← get
  if amount > available then throw .resource
  set (available - amount)

private def chargeStatic {arity} : Nat → Static.Expression arity → Admission Unit
  | 0, _ => throw .resource
  | depth + 1, value => do
      consume
      match value with
      | .literal _ | .parameter _ => pure ()
      | .add a b | .multiply a b => chargeStatic depth a; chargeStatic depth b
      | .pow2 exponent => chargeStatic depth exponent

/-- Charge traversal before substitution allocates an instantiated expression.
Referenced templates are charged separately when their uses are expanded. -/
private def chargeBody {domains scope arity} (source : Expression domains scope arity) : Admission Unit := do
  consume
  match source with
  | .nominal _ name arguments =>
      consume name.utf8ByteSize
      arguments.forM (chargeStatic 65)
  | .product elements =>
      elements.forM fun element => do
        consume
        element.arguments.forM (chargeStatic 65)
  | .fin count => chargeStatic 65 count
  | .vector element count =>
      chargeStatic 65 count
      element.arguments.forM (chargeStatic 65)
  | .polynomial _ variables degree _ | .residual _ variables degree =>
      chargeStatic 65 variables
      chargeStatic 65 degree

def normalize {arity} (expression : Static.Expression arity) : Admission (Static.Normalized expression) :=
  fun available => ((Static.normalizeM expression).run available).mapError Error.static

def normalizeArguments {arity} : (arguments : List (Static.Expression arity)) → Admission
    { normalized : List (Static.Expression arity) //
      ∀ values, normalized.map (·.eval values) = arguments.map (·.eval values) }
  | [] => return ⟨[], fun _ => rfl⟩
  | first :: rest => do
      consume
      let first ← normalize first
      let rest ← normalizeArguments rest
      return ⟨first.expression :: rest.val, fun values => by simp [first.sound values, rest.property values]⟩

variable {domains : Nat} {meaning : TypeSyntax.Interpretation domains}
  {check : DomainCheck domains} {scope : List Nat} {arity : Nat}

/-- Each reference chooses an actual earlier declaration. The callback returns
its expanded type under the supplied substitution, with that exact meaning. -/
abbrev Environment (meaning : TypeSyntax.Interpretation domains) (check : DomainCheck domains)
    (env : TypeSyntax.Environment scope) :=
  {target count : Nat} → Nat → (reference : Var scope count) → (parameters : Fin count → Static.Expression target) →
    Admission (Expanded meaning check (fun values => env reference (fun index => (parameters index).eval values)))

def use {env : TypeSyntax.Environment scope} (expanded : Environment meaning check env) (fuel : Nat)
    (source : Use scope arity) : Admission (Expanded meaning check (source.denote env)) := do
  consume (1 + source.declaration.index + source.target ^ 2)
  let arguments ← normalizeArguments source.arguments
  have length : arguments.val.length = source.target := by
    have h := congrArg List.length (arguments.property (fun _ => 0))
    simpa [source.argumentCount] using h
  let parameters : Fin source.target → Static.Expression arity :=
    fun index => arguments.val[index.val]'(by rw [length]; exact index.isLt)
  let result ← expanded fuel source.declaration parameters
  return ⟨result.shape, fun values => by
    rw [result.sound values]
    unfold Use.denote
    congr 1
    funext index
    have h := List.getElem_of_eq (arguments.property values)
      (i := index.val) (by simp [length, index.isLt])
    simpa [parameters, Use.parameters] using h, result.formed, result.measured⟩

private theorem product_denote (shapes : List (Shape domains arity)) (values : Fin arity → Nat) :
    denote meaning (.product shapes) values = productTypes (shapes.map (fun shape => denote meaning shape values)) := by
  induction shapes with
  | nil => rfl
  | cons first rest ih => exact congrArg (fun tail => denote meaning first values × tail) ih

structure ExpandedList (meaning : TypeSyntax.Interpretation domains) (check : DomainCheck domains)
    (sources : List ((Fin arity → Nat) → Type)) where
  shapes : List (Shape domains arity)
  sound : ∀ values, shapes.map (fun shape => denote meaning shape values) = sources.map (· values)
  formed : ∀ shape ∈ shapes, Formed check shape
  measured : Values Data.capacity.Measured shapes

def uses {env : TypeSyntax.Environment scope} (expanded : Environment meaning check env) (fuel : Nat) :
    (sources : List (Use scope arity)) → Admission
      (ExpandedList meaning check (sources.map (fun source values => source.denote env values)))
  | [] => return ⟨[], fun _ => rfl, by simp, .nil⟩
  | first :: rest => do
      let first ← use expanded fuel first
      let rest ← uses expanded fuel rest
      return ⟨first.shape :: rest.shapes, fun values => by simp [first.sound values, rest.sound values],
        by simpa using And.intro first.formed rest.formed, .cons first.measured rest.measured⟩

def expression {env : TypeSyntax.Environment scope} (check : DomainCheck domains)
    (expanded : Environment meaning check env) (fuel : Nat) (source : Expression domains scope arity) :
    Admission (Expanded meaning check (fun values => source.denote meaning env values)) := do
  consume
  match hsource : source with
  | .nominal domain constructor arguments =>
      let arguments ← normalizeArguments arguments
      let atom := Atom.nominal domain constructor arguments.val
      let some measured := Data.capacity.measure (.atom atom) | throw .resource
      if admitted : check atom = true then
        return ⟨.atom atom, fun values => by
          simp [denote, atom, Data.Shape.Value, Atom.denote, Expression.denote, hsource, arguments.property values],
          .atom atom admitted, measured⟩
      else throw .domain
  | .product elements =>
      let elements ← uses expanded fuel elements
      let some measured := Data.capacity.measureProduct elements.measured | throw .resource
      return ⟨.product elements.shapes, fun values => by
        rw [product_denote, elements.sound values, hsource]
        simp only [List.map_map, Function.comp_def, Expression.denote],
        .product elements.formed, measured⟩
  | .fin count =>
      let count ← normalize count
      let some measured := Data.capacity.measure (.fin count.expression) | throw .resource
      return ⟨.fin count.expression, fun values => by
        simp [denote, Data.Shape.Value, Expression.denote, hsource, count.sound values], .fin count.expression, measured⟩
  | .vector element count =>
      let count ← normalize count
      let element ← use expanded fuel element
      let some measured := Data.capacity.measureVector element.measured count.expression | throw .resource
      return ⟨.vector element.shape count.expression, fun values => by
        change (Fin (count.expression.eval values) → denote meaning element.shape values) = _
        rw [count.sound values, element.sound values, hsource]; rfl,
        .vector element.formed count.expression, measured⟩
  | .polynomial domain variables degree convention =>
      let variables ← normalize variables
      let degree ← normalize degree
      let atom := Atom.polynomial domain variables.expression degree.expression convention
      let some measured := Data.capacity.measure (.atom atom) | throw .resource
      if admitted : check atom = true then
        return ⟨.atom atom, fun values => by
          simp [denote, atom, Data.Shape.Value, Atom.denote, Expression.denote, hsource, variables.sound values, degree.sound values],
          .atom atom admitted, measured⟩
      else throw .domain
  | .residual domain variables degree =>
      let variables ← normalize variables
      let degree ← normalize degree
      let atom := Atom.residual domain variables.expression degree.expression
      let some measured := Data.capacity.measure (.atom atom) | throw .resource
      if admitted : check atom = true then
        return ⟨.atom atom, fun values => by
          simp [denote, atom, Data.Shape.Value, Atom.denote, Expression.denote, hsource, variables.sound values, degree.sound values],
          .atom atom admitted, measured⟩
      else throw .domain

private def snoc {count : Nat} {last : (Fin count → Nat) → Type}
    (value : {target : Nat} → Nat → (parameters : Fin count → Static.Expression target) →
      Admission (Expanded meaning check (fun values => last (fun index => (parameters index).eval values)))) :
    {scope : List Nat} → {env : TypeSyntax.Environment scope} → Environment meaning check env →
      Environment meaning check (TypeSyntax.Environment.snoc last env)
  | [], _, _, _, _, fuel, .here => value fuel
  | _ :: _, _, env, _, _, fuel, .here => env fuel .here
  | _ :: _, _, env, _, _, fuel, .there ref => snoc value (fun fuel v => env fuel (.there v)) fuel ref

def templates (check : DomainCheck domains) : {scope : List Nat} →
    (source : Templates domains scope) → Environment meaning check (source.denote meaning)
  | _, .nil => fun _ reference => nomatch reference
  | _, .snoc previous _ body =>
      let earlier : Environment meaning check (previous.denote meaning) := templates check previous
      snoc (fun fuel parameters => do
        match fuel with
        | 0 => throw .resource
        | fuel + 1 =>
          chargeBody body
          let result ← expression check earlier fuel (body.substitute parameters)
          return ⟨result.shape, fun values =>
            (result.sound values).trans (Expression.denote_substitute meaning _ body parameters values), result.formed, result.measured⟩) earlier

def instantiate {scope : List Nat} (check : DomainCheck domains) (source : Templates domains scope)
    (request : Use scope arity) (budget : Nat := 1000000) :
    Except Error (Expanded meaning check (request.denote (source.denote meaning))) :=
  (do
    if scope.length > 4096 then throw Error.resource
    consume scope.length
    use (templates check source) 65 request).run' (min budget 1000000)

end Zkc.Source.Mathematical.TypeExpansion
