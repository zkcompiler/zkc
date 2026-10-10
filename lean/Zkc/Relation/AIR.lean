import Zkc.Semantics.Relation
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A finite, noncyclic arithmetic AIR view. Constraints retain actual row
offsets, first/last/transition scopes, public values, read sets and degree.
This is a library relation, not an extension to PIR execution or an R1CS flattening.
Lookup/permutation arguments, challenge phases, preprocessing and quotient/PCS
construction have no representation here and require a separate adapter.
-/

set_option autoImplicit false

namespace Zkc.Relation.AIR

inductive Expr (F : Type) (publicCount columns : Nat) where
  | constant (value : F)
  | publicInput (index : Fin publicCount)
  | read (offset : Nat) (column : Fin columns)
  | add (left right : Expr F publicCount columns)
  | mul (left right : Expr F publicCount columns)

namespace Expr

variable {F : Type} [CommRing F] {p c : Nat}

def eval (statement : Fin p → F) (read : Nat × Fin c → F) : Expr F p c → F
  | .constant value => value
  | .publicInput index => statement index
  | .read offset column => read (offset, column)
  | .add left right => left.eval statement read + right.eval statement read
  | .mul left right => left.eval statement read * right.eval statement read

def reads : Expr F p c → List (Nat × Fin c)
  | .constant _ | .publicInput _ => []
  | .read offset column => [(offset, column)]
  | .add left right | .mul left right => left.reads ++ right.reads

def maxOffset : Expr F p c → Nat
  | .constant _ | .publicInput _ => 0
  | .read offset _ => offset
  | .add left right | .mul left right => max left.maxOffset right.maxOffset

/-- Degree in trace reads; public values are constants at the fixed statement. -/
def degree : Expr F p c → Nat
  | .constant _ | .publicInput _ => 0
  | .read _ _ => 1
  | .add left right => max left.degree right.degree
  | .mul left right => left.degree + right.degree

omit [CommRing F] in
theorem read_le_maxOffset (e : Expr F p c) (r : Nat × Fin c) (h : r ∈ e.reads) :
    r.1 ≤ e.maxOffset := by
  induction e with
  | constant _ | publicInput _ => simp [reads] at h
  | read offset column =>
      have eq : r = (offset, column) := by simpa [reads] using h
      simp [eq, maxOffset]
  | add left right ihl ihr | mul left right ihl ihr =>
      rcases List.mem_append.mp h with hl | hr
      · exact (ihl hl).trans (Nat.le_max_left _ _)
      · exact (ihr hr).trans (Nat.le_max_right _ _)

/-- The actual syntax derives opening/read obligations. Agreement at just
these coordinates suffices, even if every other trace cell is different. -/
theorem eval_local (e : Expr F p c) (statement : Fin p → F)
    (left right : Nat × Fin c → F) (agree : ∀ r ∈ e.reads, left r = right r) :
    e.eval statement left = e.eval statement right := by
  induction e with
  | constant _ | publicInput _ => rfl
  | read offset column => exact agree (offset, column) (by simp [reads])
  | add a b iha ihb =>
      exact congrArg₂ (· + ·) (iha fun r h => agree r (List.mem_append_left _ h))
        (ihb fun r h => agree r (List.mem_append_right _ h))
  | mul a b iha ihb =>
      exact congrArg₂ (· * ·) (iha fun r h => agree r (List.mem_append_left _ h))
        (ihb fun r h => agree r (List.mem_append_right _ h))

noncomputable def polynomial (statement : Fin p → F) (read : Nat × Fin c → Polynomial F) :
    Expr F p c → Polynomial F
  | .constant value => Polynomial.C value
  | .publicInput index => Polynomial.C (statement index)
  | .read offset column => read (offset, column)
  | .add left right => left.polynomial statement read + right.polynomial statement read
  | .mul left right => left.polynomial statement read * right.polynomial statement read

theorem polynomial_eval (e : Expr F p c) (statement : Fin p → F)
    (read : Nat × Fin c → Polynomial F) (point : F) :
    Polynomial.eval point (e.polynomial statement read) =
      e.eval statement (fun r => Polynomial.eval point (read r)) := by
  induction e <;> simp [polynomial, eval, *]

/-- If each opened trace polynomial has degree at most D, this is a genuine
polynomial degree bound for the expression. Boundary selector degrees and
division by a vanishing polynomial are additional protocol obligations. -/
theorem polynomial_degree (e : Expr F p c) (statement : Fin p → F)
    (read : Nat × Fin c → Polynomial F) (D : Nat)
    (bound : ∀ r ∈ e.reads, (read r).natDegree ≤ D) :
    (e.polynomial statement read).natDegree ≤ e.degree * D := by
  induction e with
  | constant value | publicInput value => simp [polynomial, degree]
  | read offset column => simpa [polynomial, degree] using bound (offset, column) (by simp [reads])
  | add left right ihl ihr =>
      have hl := ihl (fun r h => bound r (List.mem_append_left _ h))
      have hr := ihr (fun r h => bound r (List.mem_append_right _ h))
      exact (Polynomial.natDegree_add_le _ _).trans (max_le
        (hl.trans (Nat.mul_le_mul_right D (Nat.le_max_left _ _)))
        (hr.trans (Nat.mul_le_mul_right D (Nat.le_max_right _ _))))
  | mul left right ihl ihr =>
      have hl := ihl (fun r h => bound r (List.mem_append_left _ h))
      have hr := ihr (fun r h => bound r (List.mem_append_right _ h))
      simpa [polynomial, degree, Nat.add_mul] using
        Polynomial.natDegree_mul_le.trans (Nat.add_le_add hl hr)

def traceRead {height : Nat} (trace : Fin height → Fin c → F) (row : Fin height)
    (r : Nat × Fin c) : F :=
  if h : row.val + r.1 < height then trace ⟨row.val + r.1, h⟩ r.2 else 0

/-- Out-of-range windows fail closed; they are never cyclically wrapped. -/
def evaluateAt {height : Nat} (e : Expr F p c) (statement : Fin p → F)
    (trace : Fin height → Fin c → F) (row : Fin height) : Option F :=
  if row.val + e.maxOffset < height then some (e.eval statement (traceRead trace row)) else none

omit [CommRing F] in
theorem used_read_in_range {height : Nat} (e : Expr F p c) (row : Fin height)
    (fits : row.val + e.maxOffset < height) (r : Nat × Fin c) (h : r ∈ e.reads) :
    row.val + r.1 < height :=
  (Nat.add_le_add_left (e.read_le_maxOffset r h) row.val).trans_lt fits

theorem evaluateAt_refused {height : Nat} (e : Expr F p c) (statement : Fin p → F)
    (trace : Fin height → Fin c → F) (row : Fin height)
    (outside : height ≤ row.val + e.maxOffset) : e.evaluateAt statement trace row = none := by
  simp [evaluateAt, Nat.not_lt.mpr outside]

end Expr

inductive Scope where
  | every
  | first
  | last
  | transition (lookahead : Nat)
  deriving DecidableEq

def Scope.Active {height : Nat} (scope : Scope) (row : Fin height) : Prop :=
  match scope with
  | .every => True
  | .first => row.val = 0
  | .last => row.val + 1 = height
  | .transition lookahead => row.val + lookahead < height

instance {height : Nat} (scope : Scope) (row : Fin height) : Decidable (scope.Active row) := by
  cases scope <;> unfold Scope.Active <;> infer_instance

structure Constraint (F : Type) (publicCount columns : Nat) where
  scope : Scope
  expression : Expr F publicCount columns

variable {F : Type} [CommRing F] {p c height : Nat}

def Constraint.Holds (constraint : Constraint F p c) (statement : Fin p → F)
    (trace : Fin height → Fin c → F) : Prop :=
  ∀ row, constraint.scope.Active row → constraint.expression.evaluateAt statement trace row = some 0

/-- A real trace is nonempty. For a one-row trace, first and last both apply.
An underspecified transition window cannot bypass range checking in `Holds`. -/
def family (constraints : List (Constraint F p c)) (height : Nat) : PIR.Relation.Family where
  Statement := Fin p → F
  Witness := Fin (height + 1) → Fin c → F
  holds statement trace := ∀ constraint ∈ constraints, constraint.Holds statement trace

theorem transition_last_inactive (lookahead : Nat) (positive : 0 < lookahead) :
    ¬ (Scope.transition lookahead).Active (Fin.last height) := by
  simp only [Scope.Active, Fin.val_last]
  omega

theorem last_active : Scope.last.Active (Fin.last height) := rfl

omit [CommRing F] in
/-- The declared transition window must cover the expression's actual reads.
This law makes that condition sufficient for every active row's range guard. -/
theorem transition_window_fits (e : Expr F p c) (lookahead : Nat)
    (covers : e.maxOffset ≤ lookahead) (row : Fin height)
    (active : (Scope.transition lookahead).Active row) : row.val + e.maxOffset < height :=
  (Nat.add_le_add_left covers row.val).trans_lt active

end Zkc.Relation.AIR
