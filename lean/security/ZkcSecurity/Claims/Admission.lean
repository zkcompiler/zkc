module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Claims.Expressions
public import ZkcSecurity.Claims.Subject

@[expose] public section

/-! Numeric admission over the selected domain interpretation.
Only nominal identities in the admitted unit are available. Cardinality is read
from its actual carrier; catalogue moduli are characteristic facts. Uniform
endpoints use a specialization of the same normalizer. Static numeric parameters
need a checked binding export and are currently unsupported.
-/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source.Structured

namespace Numeric

def cardinality (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String) :
    Except Incomplete Nat :=
  match snapshot.catalogue.identitySort identity with
  | some .field => .ok (Fintype.card F)
  | some _ => .error ⟨["unsupported cardinality carrier: " ++ identity]⟩
  | none => .error ⟨["unadmitted nominal domain: " ++ identity]⟩

/-- Cardinality is taken from the carrier of each admitted nominal field.
The catalogue modulus is not the cardinality of an extension field. -/
def cardinalityOn (carriers : Carriers) (finite : ∀ d, Fintype (carriers.Field d))
    (snapshot : Snapshot) (identity : String) : Except Incomplete Nat :=
  match snapshot.catalogue.identitySort identity with
  | some .field => .ok (@Fintype.card (carriers.Field identity) (finite identity))
  | some _ => .error ⟨["unsupported cardinality carrier: " ++ identity]⟩
  | none => .error ⟨["unadmitted nominal domain: " ++ identity]⟩

/-- One arithmetic normalizer serves all carrier interpretations. The supplied
cardinality function belongs to the selected model, never to proof evidence. -/
def normalizeWith (cardinality : String → Except Incomplete Nat) :
    Wire.Expr → Except Incomplete Wire.Expr
  | .natural value => .ok (.natural value)
  | .reference name => .error ⟨["unbound numeric parameter: " ++ name]⟩
  | .application "cardinality" none [(none, .reference identity)] =>
      Wire.Expr.natural <$> cardinality identity
  | .application name _ _ => .error ⟨["numeric application: " ++ name]⟩
  | .binary operator left right => do
      return .binary operator (← normalizeWith cardinality left) (← normalizeWith cardinality right)
  | .neg operand => do return .neg (← normalizeWith cardinality operand)
  | .list _ => .error ⟨["scalar expression"]⟩

def naturalWith (cardinality : String → Except Incomplete Nat) : Wire.Expr → Except Incomplete Nat
  | .natural value => .ok value
  | .application "cardinality" none [(none, .reference identity)] => cardinality identity
  | expression => do evaluateNatural (fun _ => none) (← normalizeWith cardinality expression)

def nonnegativeWith (cardinality : String → Except Incomplete Nat) (expression : Wire.Expr) :
    Except Incomplete ℚ≥0 := do
  let value ← evaluateNonnegative (fun _ => none) (← normalizeWith cardinality expression)
  return ⟨value.val, value.property⟩

/-- Uniform-model specialization of the shared arithmetic normalizer. -/
def normalize (F : Type) [Fintype F] (snapshot : Snapshot) :=
  normalizeWith (cardinality F snapshot)

def natural (F : Type) [Fintype F] (snapshot : Snapshot) :=
  naturalWith (cardinality F snapshot)

def nonnegative (F : Type) [Fintype F] (snapshot : Snapshot) :=
  nonnegativeWith (cardinality F snapshot)

@[simp] theorem cardinalityOn_field (carriers : Carriers)
    (finite : ∀ d, Fintype (carriers.Field d)) (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    cardinalityOn carriers finite snapshot identity =
      .ok (@Fintype.card (carriers.Field identity) (finite identity)) := by
  simp [cardinalityOn, admitted]

@[simp] theorem nonnegativeWith_natural (cardinality : String → Except Incomplete Nat)
    (value : Nat) : nonnegativeWith cardinality (.natural value) = .ok (value : ℚ≥0) := by
  simp [nonnegativeWith, normalizeWith, evaluateNonnegative, evaluate]
  rfl

@[simp] theorem nonnegativeWith_cardinality (cardinality : String → Except Incomplete Nat)
    (identity : String) (count : Nat) (selected : cardinality identity = .ok count) :
    nonnegativeWith cardinality (.application "cardinality" none [(none, .reference identity)]) =
      .ok (count : ℚ≥0) := by
  simp [nonnegativeWith, normalizeWith, selected, evaluateNonnegative, evaluate]
  rfl

@[simp] theorem cardinality_field (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    cardinality F snapshot identity = .ok (Fintype.card F) := by
  simp [cardinality, admitted]

@[simp] theorem normalize_cardinality (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    normalize F snapshot (.application "cardinality" none [(none, .reference identity)]) =
      .ok (.natural (Fintype.card F)) := by simp [normalize, normalizeWith, admitted]

@[simp] theorem nonnegative_natural (F : Type) [Fintype F] (snapshot : Snapshot) (value : Nat) :
    nonnegative F snapshot (.natural value) = .ok (value : ℚ≥0) := by
  exact nonnegativeWith_natural _ _

@[simp] theorem nonnegative_cardinality (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    nonnegative F snapshot (.application "cardinality" none [(none, .reference identity)]) =
      .ok (Fintype.card F : ℚ≥0) := by
  exact nonnegativeWith_cardinality _ _ _ (cardinality_field F snapshot identity admitted)

end Numeric

inductive ContextCoverage where
  | fixed | parameter
  deriving DecidableEq, Repr

/-- A registered model context is data bound before proof search. For parameter
coverage the declaration exporting a receipt retains a String binder; a fixed
context export only covers its registered value. -/
structure ApplicationBinding where
  symbol : String
  value : String
  coverage : ContextCoverage
  deriving DecidableEq, Repr

structure ModelContext where
  application : Option ApplicationBinding := none
  deriving DecidableEq, Repr

def ModelContext.empty : ModelContext := ⟨none⟩
def ModelContext.parameter (symbol value : String) : ModelContext := ⟨some ⟨symbol, value, .parameter⟩⟩
def ModelContext.fixed (name value : String) : ModelContext := ⟨some ⟨name, value, .fixed⟩⟩

def ModelContext.resolveApplication (context : ModelContext) (symbol : String) :
    Except ResolutionError ApplicationBinding :=
  match context.application with
  | some binding => if binding.symbol = symbol then .ok binding
      else .error (.schema ("unbound application context: " ++ symbol))
  | none => .error (.schema ("unbound application context: " ++ symbol))

end ZkcSecurity.Claims

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``ZkcSecurity.Claims.Numeric.natural
  discard <| Lean.Meta.getEqnsFor? ``ZkcSecurity.Claims.Numeric.naturalWith
