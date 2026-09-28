import Zkc.Source.Mathematical.StaticNormalization

/-! Authored static expressions resolved under an explicit parameter tuple.
The input syntax and the normalization certificate remain distinct. One shared
allowance is charged before scoped construction and polynomial expansion.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Static

inductive ResolutionError where
  | arity
  | scope (reason : Error)
  | normalization (reason : NormalizationError)
  deriving DecidableEq, Repr

private def chargeRaw : Nat → Raw → StateT Nat (Except ResolutionError) Unit
  | 0, _ => throw (.scope .depth)
  | depth + 1, source => do
      let available ← get
      if available = 0 then throw (.normalization .resource)
      set (available - 1)
      match source with
      | .literal _ | .parameter _ => pure ()
      | .add left right | .multiply left right => chargeRaw depth left; chargeRaw depth right
      | .pow2 exponent => chargeRaw depth exponent

structure Resolved {arity target : Nat} (parameters : Fin arity → Expression target) (raw : Raw) where
  authored : Expression arity
  erasure : authored.erase = raw
  normalized : Normalized (authored.substitute parameters)

def resolve {arity target : Nat} (parameters : Fin arity → Expression target) (raw : Raw) :
    StateT Nat (Except ResolutionError) (Resolved parameters raw) := do
  chargeRaw 65 raw
  let authored ← (decode arity 65 raw).mapError ResolutionError.scope
  let normalized ← fun budget => ((normalizeM (authored.val.substitute parameters)).run budget).mapError ResolutionError.normalization
  return ⟨authored.val, authored.property, normalized⟩

def Resolves {arity target : Nat} (parameters : Fin arity → Expression target)
    (raw : Raw) (count : Expression target) : Prop :=
  ∃ authored : Expression arity, authored.erase = raw ∧
    ∀ values, count.eval values = authored.eval (fun index => (parameters index).eval values)

theorem Resolved.valid {arity target : Nat} {parameters : Fin arity → Expression target} {raw}
    (result : Resolved parameters raw) : Resolves parameters raw result.normalized.expression :=
  ⟨result.authored, result.erasure, fun values =>
    (result.normalized.sound values).trans (Expression.eval_substitute result.authored parameters values)⟩

theorem Resolved.evaluation_unique {arity target : Nat} {parameters : Fin arity → Expression target} {raw}
    (first second : Resolved parameters raw) (values : Fin target → Nat) :
    first.normalized.expression.eval values = second.normalized.expression.eval values := by
  have same := Expression.erase_injective (first.erasure.trans second.erasure.symm)
  rw [first.normalized.sound, second.normalized.sound, same]

inductive Arguments {arity target : Nat} (parameters : Fin arity → Expression target) : List Raw → Type where
  | nil : Arguments parameters []
  | cons {source rest} (first : Resolved parameters source) (tail : Arguments parameters rest) :
      Arguments parameters (source :: rest)

def Arguments.expressions {arity target parameters} : {sources : List Raw} →
    Arguments (arity := arity) (target := target) parameters sources → List (Expression target)
  | _, .nil => []
  | _, .cons first tail => first.normalized.expression :: tail.expressions

theorem Arguments.length {arity target parameters sources}
    (arguments : Arguments (arity := arity) (target := target) parameters sources) :
    arguments.expressions.length = sources.length := by
  induction arguments with
  | nil => rfl
  | cons first tail ih => exact congrArg Nat.succ ih

theorem Arguments.evaluations_unique {arity target parameters sources}
    (first second : Arguments (arity := arity) (target := target) parameters sources) (values : Fin target → Nat) :
    first.expressions.map (·.eval values) = second.expressions.map (·.eval values) := by
  induction first with
  | nil => cases second; rfl
  | cons first rest ih =>
      cases second with
      | cons second tail =>
          simp only [expressions, List.map_cons, List.cons.injEq]
          exact ⟨first.evaluation_unique second values, ih tail⟩

def arguments {arity target : Nat} (parameters : Fin arity → Expression target) :
    (sources : List Raw) → StateT Nat (Except ResolutionError) (Arguments parameters sources)
  | [] => return .nil
  | first :: rest => do
      let first ← resolve parameters first
      let rest ← arguments parameters rest
      return .cons first rest

structure Tuple {arity target : Nat} (parameters : Fin arity → Expression target)
    (count : Nat) (sources : List Raw) where
  arguments : Arguments parameters sources
  values : List (Expression target)
  exactValues : values = arguments.expressions
  length : values.length = count

def Tuple.parameters {arity target parameters count sources}
    (tuple : Tuple (arity := arity) (target := target) parameters count sources) : Fin count → Expression target :=
  fun index => tuple.values[index.val]'(by rw [tuple.length]; exact index.isLt)

theorem Tuple.evaluations_unique {arity target parameters count sources}
    (first second : Tuple (arity := arity) (target := target) parameters count sources) (values : Fin target → Nat) :
    first.values.map (·.eval values) = second.values.map (·.eval values) := by
  rw [first.exactValues, second.exactValues]
  exact first.arguments.evaluations_unique second.arguments values

/-- Every actual argument is checked, including unused parameters. An arity
mismatch is refused before argument normalization or substitution. -/
def tuple {arity target : Nat} (parameters : Fin arity → Expression target)
    (count : Nat) (sources : List Raw) : StateT Nat (Except ResolutionError) (Tuple parameters count sources) := do
  let available ← get
  if sources.length > available then throw (.normalization .resource)
  set (available - sources.length)
  if length : sources.length = count then
    let arguments ← arguments parameters sources
    return ⟨arguments, arguments.expressions, rfl, arguments.length.trans length⟩
  else throw .arity

end Zkc.Source.Mathematical.Static
