import Std

/-! Ordered finite domains after eager operand evaluation. Composite admission
precedes iteration, including when a child is empty or its value is unused.
Lists retain positions, order and duplicates. This is an independent value and
failure model, not a source evaluator or a resource accounting model. -/

set_option autoImplicit false

namespace Zkc.FiniteComputation

/-- A finite description over already evaluated immutable operands. Nested zip
supports heterogeneous tuples of any fixed arity. Guards represent admission
checks, not computations of source operands or body callbacks. -/
inductive Domain : Type → Type 1 where
  | elements {α : Type} (items : List α) : Domain α
  | guard {α : Type} (check : Except String Unit) (domain : Domain α) : Domain α
  | zip {α β : Type} (left : Domain α) (right : Domain β) : Domain (α × β)
  | product {α β : Type} (left : Domain α) (right : Domain β) : Domain (α × β)

namespace Domain

/-- Run admission left to right before exposing any items. A first failure stops
admission; success requires every child check and every zip extent equality. -/
def enumerate {α : Type} : Domain α → Except String (List α)
  | .elements items => .ok items
  | .guard check domain => do
    check
    enumerate domain
  | .zip left right => do
    let xs ← enumerate left
    let ys ← enumerate right
    if xs.length = ys.length then .ok (xs.zip ys) else .error "finite-zip-shape"
  | .product left right => do
    let xs ← enumerate left
    let ys ← enumerate right
    return xs.flatMap fun x => ys.map fun y => (x, y)

variable {α β : Type}

/-- Success carries exact, untruncated pair order and equal extents. Applying
this theorem recursively retains every leaf of a heterogeneous multiway zip. -/
theorem zip_ok (left : Domain α) (right : Domain β) (pairs : List (α × β)) :
    (zip left right).enumerate = .ok pairs ↔
      ∃ xs ys, left.enumerate = .ok xs ∧ right.enumerate = .ok ys ∧
        xs.length = ys.length ∧ pairs = xs.zip ys := by
  cases hl : left.enumerate with
  | error code => simp [enumerate, hl, Bind.bind, Except.bind]
  | ok xs =>
    cases hr : right.enumerate with
    | error code => simp [Bind.bind, Except.bind, enumerate, hl, hr]
    | ok ys =>
      by_cases h : xs.length = ys.length <;> simp [Bind.bind, Except.bind, enumerate, hl, hr, h, eq_comm]

/-- Shape mismatch refuses independently of subsequent body use or filtering. -/
theorem zip_mismatch (left : Domain α) (right : Domain β) (xs : List α) (ys : List β)
    (hl : left.enumerate = .ok xs) (hr : right.enumerate = .ok ys)
    (shape : xs.length ≠ ys.length) :
    (zip left right).enumerate = .error "finite-zip-shape" := by
  simp [Bind.bind, Except.bind, enumerate, hl, hr, shape]

/-- Product enumeration is lexicographic, with the left coordinate outermost. -/
theorem product_ok (left : Domain α) (right : Domain β) (pairs : List (α × β)) :
    (product left right).enumerate = .ok pairs ↔
      ∃ xs ys, left.enumerate = .ok xs ∧ right.enumerate = .ok ys ∧
        pairs = xs.flatMap (fun x => ys.map fun y => (x, y)) := by
  cases hl : left.enumerate with
  | error code => simp [enumerate, hl, Bind.bind, Except.bind]
  | ok xs =>
    cases hr : right.enumerate with
    | error code => simp [Bind.bind, Except.bind, enumerate, hl, hr]
    | ok ys => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, enumerate, hl, hr, eq_comm]

/-- An empty left factor cannot suppress right admission. -/
theorem product_empty_right_error (left : Domain α) (right : Domain β) (code : String)
    (hl : left.enumerate = .ok []) (hr : right.enumerate = .error code) :
    (product left right).enumerate = .error code := by
  simp [Bind.bind, Except.bind, enumerate, hl, hr]

/-- A successful strict zip of leaves agrees with ordinary zip only after a
proof of extent equality. This is the entry point for total consumers. -/
theorem zip_elements (xs : List α) (ys : List β) (shape : xs.length = ys.length) :
    (zip (.elements xs) (.elements ys)).enumerate = .ok (xs.zip ys) := by
  simp [Bind.bind, Except.bind, enumerate, shape]

end Domain
end Zkc.FiniteComputation
