module

public import ZkcSecurity.Claims.Admission

@[expose] public section

/-! Version zero uses exactly uniform field challenges and the typed history
random oracle. Bounds are nonnegative finite rational expressions in published
parameters and one universally quantified natural query-budget symbol. Division
by a symbolic or zero denominator is explicitly unsupported. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source.Structured ZkcSecurity.Endpoint

inductive Bound where
  | constant (value : ℚ≥0)
  | queryBudget
  | add (left right : Bound)
  | sub (left right : Bound)
  | mul (left right : Bound)
  | div (numerator : Bound) (denominator : ℚ≥0)
  | pow (base : Bound) (exponent : Nat)

noncomputable def Bound.value : Bound → Nat → ENNReal
  | .constant value, _ => value
  | .queryBudget, count => (count : ENNReal)
  | .add left right, queries => left.value queries + right.value queries
  | .sub left right, queries => left.value queries - right.value queries
  | .mul left right, queries => left.value queries * right.value queries
  | .div numerator denominator, queries => numerator.value queries / (denominator : ENNReal)
  | .pow base exponent, queries => base.value queries ^ exponent

@[simp] theorem Bound.value_constant (value : ℚ≥0) (queries : Nat) :
    (Bound.constant value).value queries = (value : ENNReal) := rfl
@[simp] theorem Bound.value_query (queries : Nat) : Bound.queryBudget.value queries = (queries : ENNReal) := rfl
@[simp] theorem Bound.value_add (left right : Bound) (queries : Nat) :
    (left.add right).value queries = left.value queries + right.value queries := rfl
@[simp] theorem Bound.value_sub (left right : Bound) (queries : Nat) :
    (left.sub right).value queries = left.value queries - right.value queries := rfl
@[simp] theorem Bound.value_mul (left right : Bound) (queries : Nat) :
    (left.mul right).value queries = left.value queries * right.value queries := rfl
@[simp] theorem Bound.value_div (numerator : Bound) (denominator : ℚ≥0) (queries : Nat) :
    (numerator.div denominator).value queries = numerator.value queries / (denominator : ENNReal) := rfl
@[simp] theorem Bound.value_pow (base : Bound) (exponent queries : Nat) :
    (base.pow exponent).value queries = base.value queries ^ exponent := rfl

/-- Elaboration selects only supported finite arithmetic, never arbitrary Lean
functions printed by a generator. -/
def Bound.elaborateWith (cardinality : String → Except Incomplete Nat) (budgetSymbol : String) :
    Wire.Expr → Except Incomplete Bound
  | .natural value => .ok (.constant value)
  | .reference name =>
      if name = budgetSymbol then .ok .queryBudget else do
        return .constant (← Numeric.nonnegativeWith cardinality (.reference name))
  | .binary .add left right => do return .add (← elaborateWith cardinality budgetSymbol left) (← elaborateWith cardinality budgetSymbol right)
  | .binary .sub left right => do return .sub (← elaborateWith cardinality budgetSymbol left) (← elaborateWith cardinality budgetSymbol right)
  | .binary .mul left right => do return .mul (← elaborateWith cardinality budgetSymbol left) (← elaborateWith cardinality budgetSymbol right)
  | .binary .div left right => do
      let denominator ← Numeric.nonnegativeWith cardinality right
      if denominator = 0 then .error ⟨["nonzero denominator"]⟩
      else return .div (← elaborateWith cardinality budgetSymbol left) denominator
  | .binary .pow base exponent => do
      return .pow (← elaborateWith cardinality budgetSymbol base) (← Numeric.naturalWith cardinality exponent)
  | .application name version arguments => do
      return .constant (← Numeric.nonnegativeWith cardinality (.application name version arguments))
  | .neg _ => .error ⟨["negative bound expression"]⟩
  | .list _ => .error ⟨["scalar bound expression"]⟩

@[simp] theorem Bound.elaborateWith_natural (cardinality : String → Except Incomplete Nat)
    (budgetSymbol : String) (value : Nat) :
    Bound.elaborateWith cardinality budgetSymbol (.natural value) = .ok (.constant value) := rfl

/-- Uniform-model specialization. Mixed-domain models select the cardinality
of each actual carrier through `Numeric.cardinalityOn`. -/
abbrev Bound.elaborate (F : Type) [Fintype F] (snapshot : Snapshot) (budgetSymbol : String) :=
  elaborateWith (Numeric.cardinality F snapshot) budgetSymbol

@[simp] theorem Bound.elaborate_natural (F : Type) [Fintype F] (snapshot : Snapshot) (budgetSymbol : String) (value : Nat) :
    Bound.elaborate F snapshot budgetSymbol (.natural value) = .ok (.constant value) := rfl
@[simp] theorem Bound.elaborate_reference (F : Type) [Fintype F] (snapshot : Snapshot) (budgetSymbol name : String) :
    Bound.elaborate F snapshot budgetSymbol (.reference name) =
      (if name = budgetSymbol then .ok .queryBudget else
        Bound.constant <$> Numeric.nonnegative F snapshot (.reference name)) := rfl
@[simp] theorem Bound.elaborate_add (F : Type) [Fintype F] (snapshot : Snapshot) (budgetSymbol : String) (left right : Wire.Expr) :
    Bound.elaborate F snapshot budgetSymbol (.binary .add left right) =
      (do return .add (← Bound.elaborate F snapshot budgetSymbol left) (← Bound.elaborate F snapshot budgetSymbol right)) := rfl
@[simp] theorem Bound.elaborate_sub (F : Type) [Fintype F] (snapshot : Snapshot) (budgetSymbol : String) (left right : Wire.Expr) :
    Bound.elaborate F snapshot budgetSymbol (.binary .sub left right) =
      (do return .sub (← Bound.elaborate F snapshot budgetSymbol left) (← Bound.elaborate F snapshot budgetSymbol right)) := rfl
@[simp] theorem Bound.elaborate_mul (F : Type) [Fintype F] (snapshot : Snapshot) (budgetSymbol : String) (left right : Wire.Expr) :
    Bound.elaborate F snapshot budgetSymbol (.binary .mul left right) =
      (do return .mul (← Bound.elaborate F snapshot budgetSymbol left) (← Bound.elaborate F snapshot budgetSymbol right)) := rfl

@[simp] theorem ennreal_nnrat_natural (value : Nat) :
    ((value : ℚ≥0) : ENNReal) = (value : ENNReal) := by
  rw [← ENNReal.coe_nnratCast]
  simp

@[simp] theorem ennreal_nnrat_zero : ((0 : ℚ≥0) : ENNReal) = 0 := by
  rw [← ENNReal.coe_nnratCast]
  simp
@[simp] theorem ennreal_nnrat_one : ((1 : ℚ≥0) : ENNReal) = 1 := by
  rw [← ENNReal.coe_nnratCast]
  simp
@[simp] theorem ennreal_nnrat_ofNat (value : Nat) [value.AtLeastTwo] :
    ((ofNat(value) : ℚ≥0) : ENNReal) = ofNat(value) := by
  rw [← ENNReal.coe_nnratCast]
  simp

@[simp] theorem Bound.value_natural (value queries : Nat) :
    (Bound.constant (value : ℚ≥0)).value queries = (value : ENNReal) := by
  simp [Bound.value]

@[simp] theorem Bound.elaborate_cardinality (F : Type) [Fintype F] (snapshot : Snapshot)
    (budgetSymbol identity : String) (admitted : snapshot.catalogue.identitySort identity = some .field) :
    Bound.elaborate F snapshot budgetSymbol (.application "cardinality" none [(none, .reference identity)]) =
      .ok (.constant (Fintype.card F : ℚ≥0)) := by
  simp [elaborate, elaborateWith, Numeric.cardinality_field _ _ _ admitted]

@[simp] theorem Bound.elaborate_div_cardinality (F : Type) [Fintype F] [Nonempty F] (snapshot : Snapshot)
    (budgetSymbol identity : String) (numerator : Wire.Expr)
    (admitted : snapshot.catalogue.identitySort identity = some .field) :
    Bound.elaborate F snapshot budgetSymbol
      (.binary .div numerator (.application "cardinality" none [(none, .reference identity)])) =
      (do return .div (← Bound.elaborate F snapshot budgetSymbol numerator) (Fintype.card F : ℚ≥0)) := by
  simp [elaborate, elaborateWith, Numeric.cardinality_field _ _ _ admitted, Fintype.card_ne_zero]

inductive QueryLimit where
  | fixed (queries : Nat)
  | symbolic (name : String)
  deriving DecidableEq, Repr

def QueryLimit.allows : QueryLimit → Nat → Prop
  | .fixed count, queries => queries = count
  | .symbolic _, _ => True

structure Model where
  form : Form
  queries : QueryLimit
  budgetSymbol : String
  application : String
  validatorCost : Bound
  applicationBinding : Option ApplicationBinding := none

/-- A typed schema can be registered before its interpretation is implemented. -/
abbrev ModelRegistry := Registry ((F : Type) → Fintype F → Snapshot → Semantics →
  Wire.Application → Except ResolutionError (Except Incomplete Model))

def exactUniform : Identifier := ⟨"models.fiat_shamir", 0⟩
def forking : Identifier := ⟨"guarantees.forking", 0⟩
def chargedReduction : Identifier := ⟨"capabilities.charged_reduction", 0⟩

end ZkcSecurity.Claims
