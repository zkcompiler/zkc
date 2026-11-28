module

public import Zkc.Subject.Charges
public import Zkc.Subject.Bound
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Field.Rat

@[expose] public section
set_option autoImplicit false

/-!
What a table of caps adds up to, as a number, against a bound.

The budget of a table is the total of its root's use at the nonnegative rationals. This module
holds that number, a bound's number, and the decisions that compare them. It is no part of the
judgment with fees and imports nothing of it: the command of a challenge decides the bound of a
goal without a ceiling here (`sumsTo`), and the fee facts decide a table's budget against a
bound by the same definitions (`within`, `atBound`).

Each decision is a closed definition, so the instances that it runs on are fixed here and not
where a command is called; the kernel evaluates it.
-/

namespace Zkc.Subject
open scoped NNRat

/-- The total of each use of a table. -/
def CapTable.totals (table : CapTable) : List ℚ≥0 :=
  table.totalsIn ℚ≥0

/-- The budget of the use at a place: its total. -/
def CapTable.budgetAt (table : CapTable) (place : Nat) : ℚ≥0 :=
  table.totalAt ℚ≥0 place

/-- The budget of a table: the total of the root's use. -/
def CapTable.budget (table : CapTable) : ℚ≥0 :=
  table.budgetAt table.root

end Zkc.Subject

namespace ZkcFormal.Written.Budget
open Zkc.Core Zkc.Subject
open scoped NNRat

/-- A bound as a nonnegative rational. -/
def ratio (b : Bound) : ℚ≥0 := (b.numerator : ℚ≥0) / b.denominator

/-- Whether the table's budget is at most the bound. -/
def within (caps : CapTable) (b : Bound) : Bool := decide (caps.budget ≤ ratio b)

/-- Whether the table's budget is the bound. -/
def atBound (caps : CapTable) (b : Bound) : Bool := decide (caps.budget = ratio b)

/-- **A bound that is taken from a table is the table's**: the table counts as the stored program
does, and its budget is the bound's number. The command of a challenge evaluates it for a goal
that writes no ceiling. -/
def sumsTo {V : Vocabulary} (caps : CapTable) (p : NamedProgram V) (root : Key) (b : Bound) : Bool :=
  caps.counted p root && atBound caps b

theorem sumsTo_iff {V : Vocabulary} (caps : CapTable) (p : NamedProgram V) (root : Key) (b : Bound) :
    sumsTo caps p root b = true ↔ caps.counted p root = true ∧ caps.budget = ratio b := by
  simp [sumsTo, atBound]

end ZkcFormal.Written.Budget
