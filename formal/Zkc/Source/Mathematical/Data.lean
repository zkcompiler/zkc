import Zkc.Source.Mathematical.Graph

/-! Structural mathematical values. Registered nominal, polynomial and residual
families supply atoms; products, finite indices and vectors have built-in
meanings independent of a domain registry or physical representation.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Data

inductive Shape (Atom : Type) (Count : Type := Nat) where
  | atom (type : Atom)
  | product (elements : List (Shape Atom Count))
  | fin (count : Count)
  | vector (element : Shape Atom Count) (count : Count)
  deriving Repr

variable {Atom Count : Type}

mutual
  private def shapeDecEq [DecidableEq Atom] [DecidableEq Count] (a b : Shape Atom Count) : Decidable (a = b) :=
    match a, b with
    | .atom a, .atom b => decidable_of_iff (a = b) (by simp)
    | .fin a, .fin b => decidable_of_iff (a = b) (by simp)
    | .product a, .product b =>
        haveI := shapesDecEq a b
        decidable_of_iff (a = b) (by simp)
    | .vector a n, .vector b m =>
        haveI := shapeDecEq a b
        decidable_of_iff (a = b ∧ n = m) (by simp)
    | .atom _, .product _ | .atom _, .fin _ | .atom _, .vector .. |
      .product _, .atom _ | .product _, .fin _ | .product _, .vector .. |
      .fin _, .atom _ | .fin _, .product _ | .fin _, .vector .. |
      .vector .., .atom _ | .vector .., .product _ | .vector .., .fin _ =>
        isFalse (by intro h; cases h)
  private def shapesDecEq [DecidableEq Atom] [DecidableEq Count] (a b : List (Shape Atom Count)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        haveI := shapeDecEq x y
        haveI := shapesDecEq xs ys
        decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance [DecidableEq Atom] [DecidableEq Count] : DecidableEq (Shape Atom Count) := shapeDecEq

mutual
  @[reducible] def Shape.Value (atomic : Atom → Type) (countValue : Count → Nat) : Shape Atom Count → Type
    | .atom type => atomic type
    | .product elements => ProductValue atomic countValue elements
    | .fin count => Fin (countValue count)
    | .vector element count => Fin (countValue count) → element.Value atomic countValue
  @[reducible] def ProductValue (atomic : Atom → Type) (countValue : Count → Nat) : List (Shape Atom Count) → Type
    | [] => PUnit
    | element :: rest => element.Value atomic countValue × ProductValue atomic countValue rest
end

def product {atomic : Atom → Type} {countValue : Count → Nat} {elements : List (Shape Atom Count)} :
    Values (Shape.Value atomic countValue) elements → (Shape.product elements).Value atomic countValue
  | .nil => PUnit.unit
  | .cons value rest => (value, product rest)

def unpack {atomic : Atom → Type} {countValue : Count → Nat} : (elements : List (Shape Atom Count)) →
    (Shape.product elements).Value atomic countValue → Values (Shape.Value atomic countValue) elements
  | [], _ => .nil
  | _ :: rest, values => .cons values.1 (unpack rest values.2)

def project {atomic : Atom → Type} {countValue : Count → Nat} {elements : List (Shape Atom Count)} {ty : Shape Atom Count}
    (component : Var elements ty) (value : (Shape.product elements).Value atomic countValue) : ty.Value atomic countValue :=
  (unpack elements value).get component

@[simp] theorem unpack_product {atomic : Atom → Type} {countValue : Count → Nat} {elements : List (Shape Atom Count)}
    (values : Values (Shape.Value atomic countValue) elements) : unpack elements (product values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [product, unpack, ih]

@[simp] theorem product_unpack {atomic : Atom → Type} {countValue : Count → Nat} (elements : List (Shape Atom Count))
    (value : (Shape.product elements).Value atomic countValue) : product (unpack elements value) = value := by
  induction elements with
  | nil => cases value; rfl
  | cons ty rest ih =>
      cases value with
      | mk first tail => exact congrArg (fun value => (first, value)) (ih tail)

@[simp] theorem project_product {atomic : Atom → Type} {countValue : Count → Nat} {elements : List (Shape Atom Count)}
    {ty : Shape Atom Count} (values : Values (Shape.Value atomic countValue) elements) (component : Var elements ty) :
    project component (product values) = values.get component := by simp [project]

def productView : Shape Atom Count → Option (List (Shape Atom Count))
  | .product elements => some elements
  | _ => none

end Zkc.Source.Mathematical.Data
