import Zkc.Relation.Bundle
import Zkc.Relation.AIR.RingExpression

/-! The finite, noncyclic AIR as a one-table bundle. The table is required and
finite, its height is chosen by the statement within `[1, maxHeight]`, its one
witness group holds the trace columns, and each constraint becomes an
assertion: every → all, first → first, last → last and transition `k` →
interior `0 k`. Expressions go through the shared ring translation
`AIR.Expr.toRing`, with public coordinates and relative reads renamed to bundle
inputs.

`holds_iff` states that whole bundle satisfaction is exactly the AIR family's
relation for every nonempty height within the bound. It relates two formal
definitions; the native `embedAIR` construction is a separate implementation.
-/

set_option autoImplicit false

namespace Zkc.Relation.Bundle.FiniteAIR

open Zkc.Relation.AIR (Constraint)

variable {F : Type} {p c : Nat}

def input : Fin p ⊕ (Nat × Fin c) → Input
  | .inl index => .publicSlot index
  | .inr (offset, column) => .read 0 offset column

def term (e : AIR.Expr F p c) : Term F :=
  e.toRing.substitute fun x => .input (input x)

def scope : AIR.Scope → Scope
  | .every => .all
  | .first => .first
  | .last => .last
  | .transition lookahead => .interior 0 lookahead

def table (constraints : List (Constraint F p c)) (maxHeight : Nat) : Table F where
  optional := false
  height := .statement 1 maxHeight false
  readModel := .finite
  groups := [⟨.witness, c⟩]
  assertions := constraints.map fun k => ⟨scope k.scope, term k.expression⟩
  fieldInteractions := []
  multisetInteractions := []

def bundle (constraints : List (Constraint F p c)) (maxHeight : Nat) : Bundle F :=
  ⟨[table constraints maxHeight]⟩

/-- The statement supplies presence, the height `h + 1` and the public slots;
the witness supplies the trace as group `0`. -/
def data [Zero F] {h : Nat} (statement : Fin p → F) (trace : Fin (h + 1) → Fin c → F) :
    Data F where
  config := ⟨fun _ => 0, fun _ _ _ _ => 0⟩
  statement :=
    { present := fun _ => true
      height := fun _ => h + 1
      publicSlot := fun i => if hi : i < p then statement ⟨i, hi⟩ else 0
      cell := fun _ _ _ _ => 0 }
  witness := ⟨fun _ _ column row =>
    if hr : row < h + 1 then if hc : column < c then trace ⟨row, hr⟩ ⟨column, hc⟩ else 0
    else 0⟩

section Expressions

variable {h : Nat} (constraints : List (Constraint F p c)) (maxHeight : Nat)

theorem term_inputs_defined (e : AIR.Expr F p c) (row : Nat) :
    (table constraints maxHeight).TermDefined (h + 1) row (term e) ↔
      ∀ r ∈ e.reads, row + r.1 < h + 1 := by
  unfold Table.TermDefined
  induction e with
  | constant value =>
      simp [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.inputs, AIR.Expr.reads]
  | publicInput index =>
      simp [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.inputs, AIR.Expr.reads, input, Table.defined]
  | read offset column =>
      simp only [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.inputs, input, List.mem_singleton, forall_eq,
        AIR.Expr.reads]
      simp only [Table.defined, table, List.getElem?_cons_zero, column.isLt,
        decide_true, Bool.true_and, resolve]
      constructor
      · intro defined
        split at defined
        · rename_i fits
          omega
        · simp at defined
      · intro fits
        rw [if_pos (by omega)]
        rfl
  | add left right ihl ihr | mul left right ihl ihr =>
      simp only [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.inputs, List.mem_append, AIR.Expr.reads] at ihl ihr ⊢
      constructor
      · intro all r mem
        rcases mem with mem | mem
        · exact (ihl.mp fun x hx => all x (Or.inl hx)) r mem
        · exact (ihr.mp fun x hx => all x (Or.inr hx)) r mem
      · intro all x mem
        rcases mem with mem | mem
        · exact (ihl.mpr fun r hr => all r (Or.inl hr)) x mem
        · exact (ihr.mpr fun r hr => all r (Or.inr hr)) x mem

/-- The maximum offset is either zero or attained by an actual read. -/
theorem maxOffset_attained (e : AIR.Expr F p c) :
    e.maxOffset = 0 ∨ ∃ r ∈ e.reads, r.1 = e.maxOffset := by
  induction e with
  | constant | publicInput => simp [AIR.Expr.maxOffset]
  | read offset column => exact Or.inr ⟨(offset, column), by simp [AIR.Expr.reads],
      by simp [AIR.Expr.maxOffset]⟩
  | add left right ihl ihr | mul left right ihl ihr =>
      simp only [AIR.Expr.maxOffset, AIR.Expr.reads, List.mem_append]
      rcases Nat.le_total left.maxOffset right.maxOffset with le | le
      · rw [Nat.max_eq_right le]
        rcases ihr with zero | ⟨r, mem, eq⟩
        · exact Or.inl zero
        · exact Or.inr ⟨r, Or.inr mem, eq⟩
      · rw [Nat.max_eq_left le]
        rcases ihl with zero | ⟨r, mem, eq⟩
        · exact Or.inl zero
        · exact Or.inr ⟨r, Or.inl mem, eq⟩

theorem reads_fit_iff (e : AIR.Expr F p c) (row height : Nat) (inside : row < height) :
    (∀ r ∈ e.reads, row + r.1 < height) ↔ row + e.maxOffset < height := by
  constructor
  · intro fits
    rcases maxOffset_attained e with zero | ⟨r, mem, eq⟩
    · simpa [zero] using inside
    · simpa [eq] using fits r mem
  · intro fits r mem
    exact (Nat.add_le_add_left (e.read_le_maxOffset r mem) row).trans_lt fits

theorem term_eval [CommRing F] (statement : Fin p → F) (trace : Fin (h + 1) → Fin c → F)
    (e : AIR.Expr F p c) (row : Fin (h + 1))
    (fits : ∀ r ∈ e.reads, row.val + r.1 < h + 1) :
    (term e).eval ((table constraints maxHeight).valuation 0 (data statement trace) (h + 1)
        row.val) = e.eval statement (AIR.Expr.traceRead trace row) := by
  induction e with
  | constant value =>
      simp [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.eval, AIR.Expr.eval]
  | publicInput index =>
      simp [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.eval, AIR.Expr.eval, input, Table.valuation, data]
  | read offset column =>
      have inside : row.val + offset < h + 1 := fits (offset, column) (by simp [AIR.Expr.reads])
      simp only [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.eval, AIR.Expr.eval, input, Table.valuation, table,
        resolve]
      rw [if_pos (by omega)]
      simp only [Table.cell, List.getElem?_cons_zero, data, AIR.Expr.traceRead]
      have cast : (((row.val : Int) + (offset : Int)).toNat) = row.val + offset := by omega
      simp [cast, inside, column.isLt]
  | add left right ihl ihr =>
      simp only [AIR.Expr.reads, List.mem_append] at fits
      simp only [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.eval, AIR.Expr.eval] at ihl ihr ⊢
      rw [ihl fun r mem => fits r (Or.inl mem), ihr fun r mem => fits r (Or.inr mem)]
  | mul left right ihl ihr =>
      simp only [AIR.Expr.reads, List.mem_append] at fits
      simp only [term, AIR.Expr.toRing, Algebra.RingExpression.Expr.substitute,
        Algebra.RingExpression.Expr.eval, AIR.Expr.eval] at ihl ihr ⊢
      rw [ihl fun r mem => fits r (Or.inl mem), ihr fun r mem => fits r (Or.inr mem)]

end Expressions

theorem scope_active (k : AIR.Scope) {h : Nat} (row : Fin (h + 1)) :
    (scope k).Active (h + 1) row.val ↔ k.Active row := by
  cases k <;> simp [scope, Scope.Active, AIR.Scope.Active]

theorem scope_defined (k : AIR.Scope) (height : Nat) : (scope k).Defined height := by
  cases k <;> simp [scope, Scope.Defined]

theorem assertion_iff [CommRing F] {h : Nat} (constraints : List (Constraint F p c))
    (maxHeight : Nat) (statement : Fin p → F) (trace : Fin (h + 1) → Fin c → F)
    (k : Constraint F p c) :
    (table constraints maxHeight).AssertionHolds 0 (data statement trace) (h + 1)
        ⟨scope k.scope, term k.expression⟩ ↔ k.Holds statement trace := by
  unfold Table.AssertionHolds Constraint.Holds
  simp only [scope_defined, true_and]
  constructor
  · intro holds row active
    obtain ⟨defined, zero⟩ := holds row.val row.isLt ((scope_active k.scope row).mpr active)
    have fits := (term_inputs_defined constraints maxHeight k.expression row.val).mp defined
    unfold AIR.Expr.evaluateAt
    rw [if_pos ((reads_fit_iff k.expression row.val (h + 1) row.isLt).mp fits),
      ← term_eval constraints maxHeight statement trace k.expression row fits, zero]
  · intro holds row inside active
    have result := holds ⟨row, inside⟩ ((scope_active k.scope ⟨row, inside⟩).mp active)
    unfold AIR.Expr.evaluateAt at result
    split at result
    · rename_i fits
      have reads := (reads_fit_iff k.expression row (h + 1) inside).mpr fits
      refine ⟨(term_inputs_defined constraints maxHeight k.expression row).mpr reads, ?_⟩
      rw [term_eval constraints maxHeight statement trace k.expression ⟨row, inside⟩ reads]
      simpa using result
    · simp at result

/-- Whole-relation equivalence: for every height `h + 1 ≤ maxHeight`, the
bundle holds on the embedded statement and trace exactly when the finite AIR
family holds. -/
theorem holds_iff [CommRing F] [DecidableEq F] (constraints : List (Constraint F p c))
    (maxHeight h : Nat) (fits : h + 1 ≤ maxHeight) (natural : F → Nat)
    (statement : Fin p → F) (trace : Fin (h + 1) → Fin c → F) :
    (bundle constraints maxHeight).Holds natural (data statement trace) ↔
      (AIR.family constraints h).holds statement trace := by
  have noField : (bundle constraints maxHeight).fieldContributions (data statement trace) = [] := by
    simp [fieldContributions, bundle, data, Table.fieldContributions, table]
  have noMultiset :
      (bundle constraints maxHeight).multiplicities (data statement trace) = [] := by
    simp [multiplicities, bundle, data, Table.multiplicities, table]
  have balanced : FieldBalanced
      ((bundle constraints maxHeight).fieldContributions (data statement trace)) := by
    rw [noField]
    intro _ _ _
    rfl
  have multiset : MultisetHolds natural
      ((bundle constraints maxHeight).multiplicities (data statement trace)) := by
    rw [noMultiset]
    exact ⟨by simp, fun _ _ _ => rfl⟩
  have height : (table constraints maxHeight).heightOf 0 (data statement trace) = h + 1 := rfl
  change _ ↔ ∀ k ∈ constraints, k.Holds statement trace
  unfold Holds
  simp only [balanced, multiset, and_true]
  constructor
  · intro holds k mem
    obtain ⟨_, tableHolds⟩ := holds 0 (table constraints maxHeight) rfl
    have assertions := (tableHolds rfl).1
    rw [height] at assertions
    exact (assertion_iff constraints maxHeight statement trace k).mp
      (assertions _ (List.mem_map.mpr ⟨k, mem, rfl⟩))
  · intro holds t tbl found
    have : t = 0 ∧ tbl = table constraints maxHeight := by
      cases t with
      | zero => exact ⟨rfl, by simpa [bundle] using found.symm⟩
      | succ t => simp [bundle] at found
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨⟨fun _ => rfl, fun _ => ?_⟩, fun _ => ⟨?_, by simp [table], by simp [table]⟩⟩
    · exact ⟨Nat.succ_pos h, Nat.succ_le_succ (Nat.zero_le h), fits, by simp⟩
    · rw [height]
      intro a mem
      obtain ⟨k, kmem, rfl⟩ := List.mem_map.mp mem
      exact (assertion_iff constraints maxHeight statement trace k).mpr (holds k kmem)

end Zkc.Relation.Bundle.FiniteAIR
