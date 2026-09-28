import Zkc.Source.Mathematical.Static

/-! Natural-polynomial arithmetic for scoped static equality.

The algebraic layer states and proves the meaning of sorted monomial insertion,
coefficient collection and distributive multiplication. Resource-limited
admission checks sizes and coefficients before running these finite operations.
The ordering policy affects representation, never the mathematical laws.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Static.Polynomial

abbrev Monomial (Atom : Type) := List Atom
abbrev Terms (Atom : Type) := List (Nat × Monomial Atom)

variable {Atom : Type}

def monomialValue (value : Atom → Nat) : Monomial Atom → Nat
  | [] => 1
  | atom :: atoms => value atom * monomialValue value atoms

def evaluate (value : Atom → Nat) : Terms Atom → Nat
  | [] => 0
  | (coefficient, monomial) :: rest =>
      coefficient * monomialValue value monomial + evaluate value rest

def insertAtom (less : Atom → Atom → Bool) (atom : Atom) : Monomial Atom → Monomial Atom
  | [] => [atom]
  | head :: rest => if less atom head then atom :: head :: rest
      else head :: insertAtom less atom rest

theorem insertAtom_value (less : Atom → Atom → Bool) (value : Atom → Nat) (atom : Atom)
    (atoms : Monomial Atom) :
    monomialValue value (insertAtom less atom atoms) = value atom * monomialValue value atoms := by
  induction atoms with
  | nil => simp [insertAtom, monomialValue]
  | cons head rest ih =>
      simp only [insertAtom]
      split
      · rfl
      · simp [monomialValue, ih, Nat.mul_left_comm]

def multiplyMonomials (less : Atom → Atom → Bool) (left right : Monomial Atom) : Monomial Atom :=
  left.foldr (insertAtom less) right

theorem multiplyMonomials_value (less : Atom → Atom → Bool) (value : Atom → Nat)
    (left right : Monomial Atom) : monomialValue value (multiplyMonomials less left right) =
      monomialValue value left * monomialValue value right := by
  induction left with
  | nil => simp [multiplyMonomials, monomialValue]
  | cons atom rest ih =>
      simp only [multiplyMonomials, List.foldr_cons, insertAtom_value]
      change value atom * monomialValue value (multiplyMonomials less rest right) = _
      rw [ih]
      simp [monomialValue, Nat.mul_assoc]

variable [DecidableEq Atom]

def insert (less : Monomial Atom → Monomial Atom → Bool) (monomial : Monomial Atom)
    (coefficient : Nat) : Terms Atom → Terms Atom
  | [] => if coefficient = 0 then [] else [(coefficient, monomial)]
  | (other, atoms) :: rest =>
      if coefficient = 0 then (other, atoms) :: rest
      else if monomial = atoms then (coefficient + other, atoms) :: rest
      else if less monomial atoms then (coefficient, monomial) :: (other, atoms) :: rest
      else (other, atoms) :: insert less monomial coefficient rest

theorem insert_value (less : Monomial Atom → Monomial Atom → Bool) (value : Atom → Nat)
    (monomial : Monomial Atom) (coefficient : Nat) (terms : Terms Atom) :
    evaluate value (insert less monomial coefficient terms) =
      coefficient * monomialValue value monomial + evaluate value terms := by
  induction terms with
  | nil =>
      by_cases zero : coefficient = 0 <;> simp [insert, evaluate, zero]
  | cons term rest ih =>
      rcases term with ⟨other, atoms⟩
      by_cases zero : coefficient = 0
      · simp [insert, evaluate, zero]
      · by_cases same : monomial = atoms
        · simp [insert, evaluate, zero, same, Nat.add_mul, Nat.add_assoc]
        · simp only [insert, if_neg zero, if_neg same]
          split
          · rfl
          · simp [evaluate, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def add (less : Monomial Atom → Monomial Atom → Bool) (left right : Terms Atom) : Terms Atom :=
  left.foldr (fun term acc => insert less term.2 term.1 acc) right

theorem add_value (less : Monomial Atom → Monomial Atom → Bool) (value : Atom → Nat)
    (left right : Terms Atom) : evaluate value (add less left right) =
      evaluate value left + evaluate value right := by
  induction left with
  | nil => simp [add, evaluate]
  | cons term rest ih =>
      simp only [add, List.foldr_cons, insert_value]
      change term.1 * monomialValue value term.2 + evaluate value (add less rest right) = _
      rw [ih]
      simp [evaluate, Nat.add_assoc]

def scale (lessAtom : Atom → Atom → Bool) (lessMonomial : Monomial Atom → Monomial Atom → Bool)
    (coefficient : Nat) (monomial : Monomial Atom) (terms : Terms Atom) : Terms Atom :=
  terms.foldr (fun term acc =>
    insert lessMonomial (multiplyMonomials lessAtom monomial term.2) (coefficient * term.1) acc) []

theorem scale_value (lessAtom : Atom → Atom → Bool)
    (lessMonomial : Monomial Atom → Monomial Atom → Bool) (value : Atom → Nat)
    (coefficient : Nat) (monomial : Monomial Atom) (terms : Terms Atom) :
    evaluate value (scale lessAtom lessMonomial coefficient monomial terms) =
      coefficient * monomialValue value monomial * evaluate value terms := by
  induction terms with
  | nil => simp [scale, evaluate]
  | cons term rest ih =>
      simp only [scale, List.foldr_cons, insert_value, multiplyMonomials_value]
      change coefficient * term.1 * (monomialValue value monomial * monomialValue value term.2) +
        evaluate value (scale lessAtom lessMonomial coefficient monomial rest) = _
      rw [ih]
      simp [evaluate, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def multiply (lessAtom : Atom → Atom → Bool)
    (lessMonomial : Monomial Atom → Monomial Atom → Bool) (left right : Terms Atom) : Terms Atom :=
  left.foldr (fun term acc => add lessMonomial (scale lessAtom lessMonomial term.1 term.2 right) acc) []

theorem multiply_value (lessAtom : Atom → Atom → Bool)
    (lessMonomial : Monomial Atom → Monomial Atom → Bool) (value : Atom → Nat)
    (left right : Terms Atom) : evaluate value (multiply lessAtom lessMonomial left right) =
      evaluate value left * evaluate value right := by
  induction left with
  | nil => simp [multiply, evaluate]
  | cons term rest ih =>
      simp only [multiply, List.foldr_cons, add_value, scale_value]
      change term.1 * monomialValue value term.2 * evaluate value right +
        evaluate value (multiply lessAtom lessMonomial rest right) = _
      rw [ih]
      simp [evaluate, Nat.add_mul]

end Zkc.Source.Mathematical.Static.Polynomial
