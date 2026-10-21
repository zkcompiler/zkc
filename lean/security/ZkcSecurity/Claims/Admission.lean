module

public import Zkc.Claims.Expressions
public import ZkcSecurity.Claims.Subject

@[expose] public section

/-! Numeric admission for the endpoint's existing uniform domain interpretation.
Only nominal identities in this admitted unit are available. A field identity
denotes `assignment F G (.field identity)`, definitionally `F`; catalogue moduli
are characteristic facts, not substitutes for its cardinality. Static numeric
parameters need a future checked binding export and are currently unsupported.
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

/-- There is one builtin shape, in every numeric position. Versioned and
qualified applications are extension requests, not aliases for this builtin. -/
def normalize (F : Type) [Fintype F] (snapshot : Snapshot) : Wire.Expr → Except Incomplete Wire.Expr
  | .natural value => .ok (.natural value)
  | .reference name => .error ⟨["unbound numeric parameter: " ++ name]⟩
  | .application "cardinality" none [(none, .reference identity)] =>
      Wire.Expr.natural <$> cardinality F snapshot identity
  | .application name _ _ => .error ⟨["numeric application: " ++ name]⟩
  | .binary operator left right => do
      return .binary operator (← normalize F snapshot left) (← normalize F snapshot right)
  | .neg operand => do return .neg (← normalize F snapshot operand)
  | .list _ => .error ⟨["scalar expression"]⟩

def natural (F : Type) [Fintype F] (snapshot : Snapshot) : Wire.Expr → Except Incomplete Nat
  | .natural value => .ok value
  | .application "cardinality" none [(none, .reference identity)] => cardinality F snapshot identity
  | expression => do evaluateNatural (fun _ => none) (← normalize F snapshot expression)

def nonnegative (F : Type) [Fintype F] (snapshot : Snapshot) (expression : Wire.Expr) :
    Except Incomplete ℚ≥0 := do
  let value ← evaluateNonnegative (fun _ => none) (← normalize F snapshot expression)
  return ⟨value.val, value.property⟩

@[simp] theorem cardinality_field (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    cardinality F snapshot identity = .ok (Fintype.card F) := by
  simp [cardinality, admitted]

@[simp] theorem normalize_cardinality (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    normalize F snapshot (.application "cardinality" none [(none, .reference identity)]) =
      .ok (.natural (Fintype.card F)) := by simp [normalize, admitted]

@[simp] theorem nonnegative_natural (F : Type) [Fintype F] (snapshot : Snapshot) (value : Nat) :
    nonnegative F snapshot (.natural value) = .ok (value : ℚ≥0) := by
  simp [nonnegative, normalize, evaluateNonnegative, evaluate]
  rfl

@[simp] theorem nonnegative_cardinality (F : Type) [Fintype F] (snapshot : Snapshot) (identity : String)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    nonnegative F snapshot (.application "cardinality" none [(none, .reference identity)]) =
      .ok (Fintype.card F : ℚ≥0) := by
  simp [nonnegative, admitted, evaluateNonnegative, evaluate]
  rfl

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
