import Std

/-! Scoped static naturals, exact erasure and checked closed evaluation.

The mathematical meaning is in Nat. The finite admission interface refuses u64
overflow at every subexpression, including subexpressions later multiplied by
zero. Evaluation never expands a power before checking its exponent bound.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Static

def limit : Nat := 18446744073709551616
abbrev Word := Fin limit

inductive Raw where
  | literal (value : Nat)
  | parameter (index : Nat)
  | add (left right : Raw)
  | multiply (left right : Raw)
  | pow2 (exponent : Raw)
  deriving DecidableEq, Repr

inductive Expression (arity : Nat) where
  | literal (value : Word)
  | parameter (index : Fin arity)
  | add (left right : Expression arity)
  | multiply (left right : Expression arity)
  | pow2 (exponent : Expression arity)
  deriving DecidableEq, Repr

variable {arity target : Nat}

def Expression.erase : Expression arity → Raw
  | .literal value => .literal value.val
  | .parameter index => .parameter index.val
  | .add left right => .add left.erase right.erase
  | .multiply left right => .multiply left.erase right.erase
  | .pow2 exponent => .pow2 exponent.erase

theorem Expression.erase_injective {first second : Expression arity}
    (same : first.erase = second.erase) : first = second := by
  induction first generalizing second <;> cases second <;> simp_all [erase, Fin.ext_iff] <;> grind

def Expression.eval (parameters : Fin arity → Nat) : Expression arity → Nat
  | .literal value => value.val
  | .parameter index => parameters index
  | .add left right => left.eval parameters + right.eval parameters
  | .multiply left right => left.eval parameters * right.eval parameters
  | .pow2 exponent => 2 ^ exponent.eval parameters

def Expression.substitute (parameters : Fin arity → Expression target) :
    Expression arity → Expression target
  | .literal value => .literal value
  | .parameter index => parameters index
  | .add left right => .add (left.substitute parameters) (right.substitute parameters)
  | .multiply left right => .multiply (left.substitute parameters) (right.substitute parameters)
  | .pow2 exponent => .pow2 (exponent.substitute parameters)

theorem Expression.eval_substitute (expression : Expression arity)
    (parameters : Fin arity → Expression target) (values : Fin target → Nat) :
    (expression.substitute parameters).eval values =
      expression.eval (fun index => (parameters index).eval values) := by
  induction expression with
  | literal value => rfl
  | parameter index => rfl
  | add left right leftIH rightIH => simp [substitute, eval, leftIH, rightIH]
  | multiply left right leftIH rightIH => simp [substitute, eval, leftIH, rightIH]
  | pow2 exponent ih => simp [substitute, eval, ih]

inductive Error where
  | depth
  | literal
  | scope
  | overflow
  deriving DecidableEq, Repr

/-- Success returns this exact scoped expression, not just an acceptance bit. -/
def decode (arity : Nat) : (fuel : Nat) → (raw : Raw) →
    Except Error { expression : Expression arity // expression.erase = raw }
  | 0, _ => .error .depth
  | fuel + 1, raw => do
    match hraw : raw with
    | .literal value =>
      if h : value < limit then return ⟨.literal ⟨value, h⟩, by simp [Expression.erase, hraw]⟩
      else throw .literal
    | .parameter index =>
      if h : index < arity then return ⟨.parameter ⟨index, h⟩, by simp [Expression.erase, hraw]⟩
      else throw .scope
    | .add left right =>
      let a ← decode arity fuel left
      let b ← decode arity fuel right
      return ⟨.add a.val b.val, by simp [Expression.erase, a.property, b.property, hraw]⟩
    | .multiply left right =>
      let a ← decode arity fuel left
      let b ← decode arity fuel right
      return ⟨.multiply a.val b.val, by simp [Expression.erase, a.property, b.property, hraw]⟩
    | .pow2 exponent =>
      let a ← decode arity fuel exponent
      return ⟨.pow2 a.val, by simp [Expression.erase, a.property, hraw]⟩

/-- The dependent result records both the u64 bound and mathematical meaning. -/
def Expression.checked (parameters : Fin arity → Word) :
    (expression : Expression arity) →
      Except Error { value : Word // value.val = expression.eval (fun i => (parameters i).val) }
  | .literal value => return ⟨value, rfl⟩
  | .parameter index => return ⟨parameters index, rfl⟩
  | .add left right => do
    let a ← left.checked parameters
    let b ← right.checked parameters
    if h : a.val.val + b.val.val < limit then
      return ⟨⟨a.val.val + b.val.val, h⟩, by simp [Expression.eval, a.property, b.property]⟩
    else throw .overflow
  | .multiply left right => do
    let a ← left.checked parameters
    let b ← right.checked parameters
    if h : a.val.val * b.val.val < limit then
      return ⟨⟨a.val.val * b.val.val, h⟩, by simp [Expression.eval, a.property, b.property]⟩
    else throw .overflow
  | .pow2 exponent => do
    let a ← exponent.checked parameters
    if a.val.val ≥ 64 then throw .overflow
    if h : 2 ^ a.val.val < limit then
      return ⟨⟨2 ^ a.val.val, h⟩, by simp [Expression.eval, a.property]⟩
    else throw .overflow

theorem decode_erases {raw : Raw} {result} (_accepted : decode arity 65 raw = .ok result) :
    result.val.erase = raw := result.property

theorem checked_sound (parameters : Fin arity → Word) (expression : Expression arity)
    {result} (_accepted : expression.checked parameters = .ok result) :
    result.val.val < limit ∧
      result.val.val = expression.eval (fun i => (parameters i).val) :=
  ⟨result.val.isLt, result.property⟩

end Zkc.Source.Mathematical.Static
