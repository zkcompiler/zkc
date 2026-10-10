import Zkc.Algebra.RingExpression
import Zkc.Algebra.FiniteVectors
import Mathlib.LinearAlgebra.Lagrange

/-! Checked pointwise maps of ring expressions over finite vectors.

A map applies one formula at every row of its rowwise operands while scalar
operands are shared by every row. The shape check reads every rowwise operand,
used or not, before any arithmetic, and refuses when the lengths differ or no
operand is rowwise. This model states the value of a successful map, the
refusals, and three laws a realization may rely on: composed formulas can be
mapped in one pass, a subformula over scalar operands has one value for every
row, and a formula mapped over evaluations of polynomials yields evaluations of
the substituted polynomial, which interpolation recovers only below the node
count.

The subject is this list model over one commutative ring. The native vector
carrier, field identities, the native map realizer and its correspondence
checker are not modelled; no native correspondence is claimed. -/

set_option autoImplicit false

namespace Zkc.Algebra.RingExpression

open FiniteVectors (Result limit)

/-- One map operand: a scalar shared by every row or one value per row. -/
inductive Operand (F : Type) where
  | scalar (value : F)
  | rows (values : List F)
  deriving DecidableEq

namespace Operand

variable {F : Type}

/-- The row count a rowwise operand contributes; a scalar contributes none. -/
def rowLength : Operand F → Option Nat
  | .scalar _ => none
  | .rows values => some values.length

/-- The value operand `j` supplies at row `i`. Total, with zero outside the
operands or rows; successful maps never read those positions. -/
def read [Zero F] (operands : List (Operand F)) (j i : Nat) : F :=
  match operands[j]? with
  | some (.scalar value) => value
  | some (.rows values) => values[i]?.getD 0
  | none => 0

theorem read_scalar [Zero F] (operands : List (Operand F)) (j i : Nat) (value : F)
    (h : operands[j]? = some (.scalar value)) : read operands j i = value := by
  simp [read, h]

theorem read_rows [Zero F] (operands : List (Operand F)) (j i : Nat) (values : List F)
    (h : operands[j]? = some (.rows values)) (inside : i < values.length) :
    read operands j i = values[i] := by
  simp [read, h, List.getElem?_eq_getElem inside]

end Operand

/-- The common row count. Every rowwise operand is read, including operands the
formula never uses; at least one must be rowwise and all must agree. -/
def rowCount {F : Type} (operands : List (Operand F)) : Result Nat :=
  let lengths := operands.filterMap Operand.rowLength
  if lengths.all (· ≤ limit) then
    match lengths with
    | [] => .error "map-rows"
    | n :: rest => if rest.all (· == n) then .ok n else .error "vector-shape"
  else .error "vector-limit"

/-- Formula inputs name operand positions; a missing position refuses before
any row is read. -/
def map {F : Type} [CommRing F] (e : Expr F Nat) (operands : List (Operand F)) :
    Result (List F) :=
  if e.inputs.all (· < operands.length) then
    match rowCount operands with
    | .error code => .error code
    | .ok n => .ok ((List.range n).map fun i => e.eval fun j => Operand.read operands j i)
  else .error "map-signature"

section RowCount

variable {F : Type}

theorem rowCount_ok (operands : List (Operand F)) (n : Nat)
    (h : rowCount operands = .ok n) :
    n ≤ limit ∧ (∃ values : List F, .rows values ∈ operands ∧ values.length = n) ∧
      ∀ values : List F, .rows values ∈ operands → values.length = n := by
  unfold rowCount at h
  simp only at h
  split at h
  · rename_i bounded
    split at h
    · cases h
    · rename_i m rest found
      split at h
      · rename_i agree
        cases h
        have mem : ∀ k ∈ operands.filterMap Operand.rowLength, k = n := by
          intro k hk
          rw [found] at hk
          rcases List.mem_cons.mp hk with rfl | hk
          · rfl
          · simpa using List.all_eq_true.mp agree k hk
        have bound : n ≤ limit := by
          have := List.all_eq_true.mp bounded n (by rw [found]; exact List.mem_cons_self ..)
          simpa using this
        refine ⟨bound, ?_, ?_⟩
        · have : n ∈ operands.filterMap Operand.rowLength := by
            rw [found]; exact List.mem_cons_self ..
          obtain ⟨o, ho, hn⟩ := List.mem_filterMap.mp this
          cases o with
          | scalar _ => simp [Operand.rowLength] at hn
          | rows values =>
            simp only [Operand.rowLength, Option.some.injEq] at hn
            exact ⟨values, ho, hn⟩
        · intro values hv
          exact mem values.length (List.mem_filterMap.mpr ⟨.rows values, hv, rfl⟩)
      · cases h
  · cases h

/-- Two rowwise operands of different lengths refuse, whatever the formula reads. -/
theorem rowCount_shape (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length) (n : Nat) : rowCount operands ≠ .ok n := by
  intro h
  obtain ⟨_, _, agree⟩ := rowCount_ok operands n h
  exact ne ((agree left hl).trans (agree right hr).symm)

/-- Scalars alone fix no row count. -/
theorem rowCount_scalars (operands : List (Operand F))
    (h : ∀ o ∈ operands, ∃ value : F, o = .scalar value) :
    rowCount operands = .error "map-rows" := by
  have empty : operands.filterMap Operand.rowLength = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro o ho
    obtain ⟨value, rfl⟩ := h o ho
    rfl
  simp [rowCount, empty]

/-- Rowwise operands of one common bounded length succeed with that length. -/
theorem rowCount_eq (operands : List (Operand F)) (n : Nat) (bound : n ≤ limit)
    (some : ∃ values : List F, .rows values ∈ operands)
    (agree : ∀ values : List F, .rows values ∈ operands → values.length = n) :
    rowCount operands = .ok n := by
  have all : ∀ k ∈ operands.filterMap Operand.rowLength, k = n := by
    intro k hk
    obtain ⟨o, ho, hk⟩ := List.mem_filterMap.mp hk
    cases o with
    | scalar _ => simp [Operand.rowLength] at hk
    | rows values =>
      simp only [Operand.rowLength, Option.some.injEq] at hk
      exact hk ▸ agree values ho
  obtain ⟨values, hv⟩ := some
  have mem : values.length ∈ operands.filterMap Operand.rowLength :=
    List.mem_filterMap.mpr ⟨.rows values, hv, rfl⟩
  have bounded : (operands.filterMap Operand.rowLength).all (· ≤ limit) = true :=
    List.all_eq_true.mpr fun k hk => by simpa using (all k hk) ▸ bound
  unfold rowCount
  simp only [bounded, if_true]
  split
  · rename_i found
    rw [found] at mem
    simp at mem
  · rename_i m rest found
    have hm : m = n := all m (by rw [found]; exact List.mem_cons_self ..)
    have rest_agree : rest.all (· == n) = true := List.all_eq_true.mpr fun k hk => by
      simpa using all k (by rw [found]; exact List.mem_cons_of_mem _ hk)
    subst hm
    rw [if_pos rest_agree]

/-- A shape mismatch between two rowwise operands is reported as such once the
operands are within the limit. -/
theorem rowCount_shape_code (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length)
    (bounded : (operands.filterMap Operand.rowLength).all (· ≤ limit) = true) :
    rowCount operands = .error "vector-shape" := by
  have hl' : left.length ∈ operands.filterMap Operand.rowLength :=
    List.mem_filterMap.mpr ⟨.rows left, hl, rfl⟩
  have hr' : right.length ∈ operands.filterMap Operand.rowLength :=
    List.mem_filterMap.mpr ⟨.rows right, hr, rfl⟩
  unfold rowCount
  simp only [bounded, if_true]
  split
  · rename_i found
    rw [found] at hl'
    simp at hl'
  · rename_i m rest found
    rw [found] at hl' hr'
    have : ¬ rest.all (· == m) = true := by
      intro agree
      have eq : ∀ k ∈ m :: rest, k = m := fun k hk => by
        rcases List.mem_cons.mp hk with rfl | hk
        · rfl
        · simpa using List.all_eq_true.mp agree k hk
      exact ne ((eq _ hl').trans (eq _ hr').symm)
    simp [this]

end RowCount

section Map

variable {F : Type} [CommRing F]

/-- A successful map has the common row count and the row-by-row value. -/
theorem map_ok (e : Expr F Nat) (operands : List (Operand F)) (output : List F)
    (h : map e operands = .ok output) :
    (∀ j ∈ e.inputs, j < operands.length) ∧
      ∃ n, rowCount operands = .ok n ∧
        output = (List.range n).map fun i => e.eval fun j => Operand.read operands j i := by
  unfold map at h
  split at h
  · rename_i signature
    refine ⟨fun j hj => by simpa using List.all_eq_true.mp signature j hj, ?_⟩
    split at h
    · cases h
    · rename_i n found
      cases h
      exact ⟨n, found, rfl⟩
  · cases h

theorem map_eq (e : Expr F Nat) (operands : List (Operand F)) (n : Nat)
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (count : rowCount operands = .ok n) :
    map e operands =
      .ok ((List.range n).map fun i => e.eval fun j => Operand.read operands j i) := by
  have all : e.inputs.all (· < operands.length) = true :=
    List.all_eq_true.mpr fun j hj => by simpa using signature j hj
  simp [map, all, count]

/-- The output has the length of every rowwise operand. -/
theorem map_length (e : Expr F Nat) (operands : List (Operand F)) (output : List F)
    (h : map e operands = .ok output) (values : List F) (hv : .rows values ∈ operands) :
    output.length = values.length := by
  obtain ⟨_, n, count, rfl⟩ := map_ok e operands output h
  obtain ⟨_, _, agree⟩ := rowCount_ok operands n count
  simp [agree values hv]

/-- Row `i` of the output is the formula at the row-`i` values of the rowwise
operands and the shared scalars. -/
theorem map_coordinate (e : Expr F Nat) (operands : List (Operand F)) (output : List F)
    (h : map e operands = .ok output) (i : Nat) (inside : i < output.length) :
    output[i]? = some (e.eval fun j => Operand.read operands j i) := by
  obtain ⟨_, n, _, rfl⟩ := map_ok e operands output h
  simp only [List.length_map, List.length_range] at inside
  simp [List.getElem?_map, List.getElem?_range inside]

/-- Unequal rowwise lengths never succeed, including for operands the formula
never reads. -/
theorem map_shape (e : Expr F Nat) (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length) (output : List F) : map e operands ≠ .ok output := by
  intro h
  obtain ⟨_, n, count, _⟩ := map_ok e operands output h
  exact rowCount_shape operands left right hl hr ne n count

/-- With the formula well formed over the operands, the refusal is the shape code. -/
theorem map_shape_code (e : Expr F Nat) (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length)
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (bounded : (operands.filterMap Operand.rowLength).all (· ≤ limit) = true) :
    map e operands = .error "vector-shape" := by
  have all : e.inputs.all (· < operands.length) = true :=
    List.all_eq_true.mpr fun j hj => by simpa using signature j hj
  simp [map, all, rowCount_shape_code operands left right hl hr ne bounded]

/-- Scalars alone never succeed: there is no row count to map over. -/
theorem map_scalars (e : Expr F Nat) (operands : List (Operand F))
    (h : ∀ o ∈ operands, ∃ value : F, o = .scalar value) (output : List F) :
    map e operands ≠ .ok output := by
  intro ok
  obtain ⟨_, n, count, _⟩ := map_ok e operands output ok
  rw [rowCount_scalars operands h] at count
  cases count

/-- A formula input beyond the operands refuses before any row is read. -/
theorem map_signature (e : Expr F Nat) (operands : List (Operand F)) (j : Nat)
    (hj : j ∈ e.inputs) (outside : operands.length ≤ j) :
    map e operands = .error "map-signature" := by
  have : ¬ e.inputs.all (· < operands.length) = true := by
    intro all
    have := List.all_eq_true.mp all j hj
    simp at this
    omega
  simp [map, this]

/-- The map is the lane interpretation of the formula: its output at row `i` is
scalar evaluation on lane `i`. -/
theorem map_lanes (e : Expr F Nat) (operands : List (Operand F)) (output : List F)
    (h : map e operands = .ok output) :
    output = (List.range output.length).map
      ((e.map fun value (_ : Nat) => value).eval fun j i => Operand.read operands j i) := by
  obtain ⟨_, n, _, rfl⟩ := map_ok e operands output h
  simp only [List.length_map, List.length_range]
  exact List.map_congr_left fun i _ => (Expr.eval_lanes e _ i).symm

end Map

section Substitution

variable {F : Type} [CommRing F]

omit [CommRing F] in
theorem inputs_substitute {I J : Type} (e : Expr F I) (σ : I → Expr F J) :
    (e.substitute σ).inputs = e.inputs.flatMap fun i => (σ i).inputs := by
  induction e <;> simp [Expr.substitute, Expr.inputs, *]

/-- Fusion. Mapping an outer formula over the outputs of inner maps, in the
inner formulas' order, equals mapping the composed formula over the original
operands in one pass. The composed map reads the same operands, so a shape
refusal of the operands refuses it as well. -/
theorem map_substitute (e : Expr F Nat) (σ : Nat → Expr F Nat)
    (operands : List (Operand F)) (inner : Nat → List F) (m : Nat) (positive : 0 < m)
    (outer : ∀ j ∈ e.inputs, j < m)
    (maps : ∀ j < m, map (σ j) operands = .ok (inner j)) :
    map e ((List.range m).map fun j => .rows (inner j)) =
      map (e.substitute σ) operands := by
  obtain ⟨_, n, count, _⟩ := map_ok _ _ _ (maps 0 positive)
  obtain ⟨bound, _, _⟩ := rowCount_ok operands n count
  have inner_eq : ∀ j < m, inner j =
      (List.range n).map fun i => (σ j).eval fun k => Operand.read operands k i := by
    intro j hj
    obtain ⟨_, n', count', eq⟩ := map_ok _ _ _ (maps j hj)
    rw [count] at count'
    cases count'
    exact eq
  have inner_length : ∀ j < m, (inner j).length = n := by
    intro j hj
    rw [inner_eq j hj]
    simp
  have left_count : rowCount ((List.range m).map fun j => .rows (inner j)) = .ok n := by
    refine rowCount_eq _ n bound
      ⟨inner 0, List.mem_map.mpr ⟨0, by simpa using positive, rfl⟩⟩ ?_
    intro values hv
    obtain ⟨j, hj, eq⟩ := List.mem_map.mp hv
    cases eq
    exact inner_length j (List.mem_range.mp hj)
  have left_signature : ∀ j ∈ e.inputs,
      j < ((List.range m).map fun j => Operand.rows (inner j)).length := by
    intro j hj
    simpa using outer j hj
  have right_signature : ∀ j ∈ (e.substitute σ).inputs, j < operands.length := by
    intro j hj
    rw [inputs_substitute] at hj
    obtain ⟨k, hk, hj⟩ := List.mem_flatMap.mp hj
    exact (map_ok _ _ _ (maps k (outer k hk))).1 j hj
  rw [map_eq e _ n left_signature left_count,
    map_eq (e.substitute σ) operands n right_signature count]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [Expr.eval_substitute]
  apply Expr.eval_local
  intro j hj
  have hj := outer j hj
  simp [Operand.read, List.getElem?_map, List.getElem?_range hj, inner_eq j hj,
    List.getElem?_range hi]

/-- Hoisting. A subformula whose inputs are all scalar operands has the same
value at every row; replacing it by that one value, computed once, preserves
the map. -/
theorem map_hoist (e : Expr F Nat) (σ σ' : Nat → Expr F Nat) (k : Nat)
    (operands : List (Operand F)) (output : List F)
    (scalars : ∀ j ∈ (σ k).inputs, ∃ value : F, operands[j]? = some (.scalar value))
    (hoisted : σ' k = .constant ((σ k).eval fun j => Operand.read operands j 0))
    (others : ∀ j, j ≠ k → σ' j = σ j)
    (h : map (e.substitute σ) operands = .ok output) :
    map (e.substitute σ') operands = .ok output := by
  obtain ⟨signature, n, count, rfl⟩ := map_ok _ _ _ h
  have signature' : ∀ j ∈ (e.substitute σ').inputs, j < operands.length := by
    intro j hj
    apply signature
    rw [inputs_substitute] at hj ⊢
    obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp hj
    refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
    by_cases eq : i = k
    · subst eq
      rw [hoisted] at hj
      simp [Expr.inputs] at hj
    · rwa [others i eq] at hj
  rw [map_eq _ _ n signature' count]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [Expr.eval_substitute, Expr.eval_substitute]
  congr 1
  funext j
  by_cases eq : j = k
  · subst eq
    rw [hoisted]
    simp only [Expr.eval]
    apply Expr.eval_local
    intro l hl
    obtain ⟨value, hv⟩ := scalars l hl
    rw [Operand.read_scalar _ _ _ _ hv, Operand.read_scalar _ _ _ _ hv]
  · rw [others j eq]

end Substitution

section Polynomial

open _root_.Polynomial

variable {F : Type} [CommRing F]

/-- Mapping a formula over the evaluations of input polynomials at ordered
points gives the evaluations of the substituted polynomial at those points.
This is the only sense in which a pointwise map computes a formal polynomial. -/
theorem map_polynomial (e : Expr F Nat) (p : Nat → Polynomial F) (points : List F)
    (m : Nat) (positive : 0 < m) (signature : ∀ j ∈ e.inputs, j < m)
    (bound : points.length ≤ limit) :
    map e ((List.range m).map fun j => .rows (points.map fun x => (p j).eval x)) =
      .ok (points.map fun x => (e.polynomial p).eval x) := by
  have count : rowCount ((List.range m).map fun j => .rows (points.map fun x => (p j).eval x)) =
      .ok points.length := by
    refine rowCount_eq _ _ bound
      ⟨_, List.mem_map.mpr ⟨0, by simpa using positive, rfl⟩⟩ ?_
    intro values hv
    obtain ⟨j, _, eq⟩ := List.mem_map.mp hv
    cases eq
    simp
  rw [map_eq _ _ _ (fun j hj => by simpa using signature j hj) count]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, Expr.polynomial_eval]
  apply Expr.eval_local
  intro j hj
  have hj := signature j hj
  rw [Operand.read_rows _ j i (points.map fun x => (p j).eval x)
    (by simp [List.getElem?_map, List.getElem?_range hj]) (by simpa using h₁)]
  simp

end Polynomial

section Interpolation

open _root_.Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- Interpolating the pointwise values at distinct nodes recovers the substituted
polynomial if its structural degree bound is below the node count.
This sufficient bound is a premise about the input polynomials, not a fact the
values establish. An overestimated bound need not prevent recovery; the theorem
below rules out recovery when the actual polynomial degree reaches the node count. -/
theorem interpolate_polynomial (e : Expr F Nat) (p : Nat → Polynomial F)
    (nodes : Finset F) (inputDegree : Nat → Nat)
    (bound : ∀ i ∈ e.inputs, (p i).natDegree ≤ inputDegree i)
    (small : e.degree inputDegree < nodes.card) :
    Lagrange.interpolate nodes id (fun x => e.eval fun i => (p i).eval x) =
      e.polynomial p := by
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (Set.injOn_id _) ?_ ?_
  · refine lt_of_le_of_lt degree_le_natDegree ?_
    exact WithBot.coe_lt_coe.mpr
      (lt_of_le_of_lt (Expr.polynomial_degree e p inputDegree bound) small)
  · intro x _
    simp [Expr.polynomial_eval]

/-- The interpolant always has degree below the node count. A substituted
polynomial of at least that degree is therefore never the interpolant of its
own pointwise values on those nodes, however many nodes agree. -/
theorem interpolate_ne_polynomial (e : Expr F Nat) (p : Nat → Polynomial F)
    (nodes : Finset F) (large : (nodes.card : WithBot ℕ) ≤ (e.polynomial p).degree) :
    Lagrange.interpolate nodes id (fun x => e.eval fun i => (p i).eval x) ≠
      e.polynomial p := by
  intro h
  have lt := Lagrange.degree_interpolate_lt (s := nodes) (v := id)
    (fun x => e.eval fun i => (p i).eval x) (Set.injOn_id _)
  rw [h] at lt
  exact absurd (lt_of_le_of_lt large lt) (lt_irrefl _)

end Interpolation

end Zkc.Algebra.RingExpression
