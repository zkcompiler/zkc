module

public import Zkc.Source.Structured.NumericalLaws
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.List.FinRange

@[expose] public section

/-! Coefficient and node equations for the source's direct Lagrange algorithm.
The list order is the numerical evaluator's order, including the omitted node
in each basis polynomial. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Numerical
open Polynomial
variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem polynomial_add (as bs : List F) :
    ofCoeffList (add as bs) = ofCoeffList as + ofCoeffList bs := by
  induction as generalizing bs with
  | nil => simp [add]
  | cons a as ih =>
    cases bs with
    | nil => simp [add]
    | cons b bs => simp [add, ofCoeffList_cons, ih, mul_add, add_add_add_comm]

omit [DecidableEq F] in
theorem polynomial_multiply (as bs : List F) :
    ofCoeffList (multiply as bs) = ofCoeffList as * ofCoeffList bs := by
  induction as with
  | nil => simp [multiply]
  | cons a as ih =>
    rw [multiply, polynomial_add, ofCoeffList_map_mul, ofCoeffList_zero_cons, ih, ofCoeffList_cons]
    ring

omit [DecidableEq F] in
theorem polynomial_factors (xs cs : List F) :
    ofCoeffList (xs.foldl (fun acc x ↦ multiply acc [-x, 1]) cs) =
      ofCoeffList cs * (xs.map fun x ↦ X - C x).prod := by
  induction xs generalizing cs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, polynomial_multiply, List.map_cons, List.prod_cons]
    simp [ofCoeffList_cons, sub_eq_add_neg, mul_assoc, add_comm]

omit [DecidableEq F] in
theorem polynomial_sum (terms : List (List F)) (cs : List F) :
    ofCoeffList (terms.foldl add cs) = ofCoeffList cs + (terms.map ofCoeffList).sum := by
  induction terms generalizing cs with
  | nil => simp
  | cons term terms ih => simp [ih, polynomial_add, add_assoc]

omit [Field F] [DecidableEq F] in
/-- Filtering the source's indexed row omits exactly the interpolation node.
This holds for noninjective maps as well. Injectivity is required at inversion. -/
theorem other_nodes {n : Nat} (node : Fin n → F) (i : Fin n) :
    ((List.ofFn node).zipIdx.filter fun pair ↦ pair.2 != i.val).map Prod.fst =
      ((List.finRange n).filter (fun j ↦ j != i)).map node := by
  have indexed : (List.ofFn node).zipIdx =
      (List.finRange n).map (fun j ↦ (node j, j.val)) := by
    apply List.ext_getElem (by simp)
    intro j _ _
    simp [List.getElem_zipIdx, List.getElem_ofFn]
  rw [indexed, List.filter_map, List.map_map]
  congr 1

theorem other_indices {n : Nat} (i : Fin n) :
    ((List.finRange n).filter (fun j ↦ j != i)).toFinset = Finset.univ.erase i := by
  ext j
  simp

omit [Field F] [DecidableEq F] in
private theorem product_other_nodes {A : Type} [CommMonoid A] {n : Nat}
    (node : Fin n → F) (i : Fin n) (f : F → A) :
    ((((List.finRange n).filter (fun j ↦ j != i)).map node).map f).prod =
      (Finset.univ.erase i).prod (fun j ↦ f (node j)) := by
  rw [List.map_map, ← other_indices, List.prod_toFinset]
  · rfl
  · exact List.Nodup.filter _ (List.nodup_finRange n)

omit [Field F] [DecidableEq F] in
private theorem node_at {n : Nat} [Inhabited F] (f : Fin n → F) (i : Fin n) :
    (List.ofFn f)[i.val]! = f i := by
  rw [getElem!_pos _ _ (List.length_ofFn.symm ▸ i.isLt), List.getElem_ofFn]

omit [DecidableEq F] in
/-- The source's coefficient list for one term denotes its Lagrange basis
polynomial scaled by the corresponding value. Distinct nodes ensure that the
actual inversion succeeds. -/
theorem interpolationTerm_spec {n : Nat} [Inhabited F] (node value : Fin n → F)
    (injective : Function.Injective node) (invert : F → Result F)
    (inverse_ok : ∀ x ≠ 0, invert x = .ok x⁻¹) (i : Fin n) :
    ∃ cs, interpolationTerm invert (List.ofFn node) (List.ofFn value) i.val = .ok cs ∧
      ofCoeffList cs = C (value i) * Lagrange.basis Finset.univ node i := by
  let others := ((List.finRange n).filter (fun j ↦ j != i)).map node
  let denominator := (Finset.univ.erase i).prod (fun j ↦ node i - node j)
  have den : (others.map (node i - ·)).foldl (· * ·) 1 = denominator := by
    rw [← List.prod_eq_foldl]; exact product_other_nodes node i _
  have nonzero : denominator ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j h
    exact sub_ne_zero.mpr (fun eq ↦ (Finset.mem_erase.mp h).1 (injective eq).symm)
  let coefficients := others.foldl (fun acc x ↦ multiply acc [-x, 1]) [1]
  refine ⟨coefficients.map ((value i * denominator⁻¹) * ·), ?_, ?_⟩
  · simp only [interpolationTerm, other_nodes, node_at,
      bind, Except.bind, pure, Except.pure]
    rw [den, inverse_ok denominator nonzero]
    change Except.ok (coefficients.map fun a ↦ a * (value i * denominator⁻¹)) = _
    rw [show (fun a : F ↦ a * (value i * denominator⁻¹)) = ((value i * denominator⁻¹) * ·) from
      funext fun a ↦ mul_comm _ _]
  · rw [ofCoeffList_map_mul, polynomial_factors, product_other_nodes node i]
    simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, map_one, one_mul]
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib]
    rw [← map_prod,
      ← Finset.prod_inv_distrib, map_mul]
    ring

omit [DecidableEq F] in
/-- Correctness of the ordered, partial interpolation algorithm. Its actual
output represents the unique interpolant, including when every value is zero. -/
theorem interpolateAt_spec {n : Nat} [Inhabited F] (node value : Fin n → F)
    (injective : Function.Injective node) (invert : F → Result F)
    (inverse_ok : ∀ x ≠ 0, invert x = .ok x⁻¹) :
    ∃ cs, interpolateAt invert (List.ofFn node) (List.ofFn value) = .ok cs ∧
      ofCoeffList cs = Lagrange.interpolate Finset.univ node value := by
  choose term runs represents using interpolationTerm_spec node value injective invert inverse_ok
  let indices := List.finRange n
  have range_eq : List.range n = indices.map Fin.val := by
    apply List.ext_getElem (by simp [indices])
    intro j _ _
    simp [indices]
  have traversal : (List.range n).mapM
      (interpolationTerm invert (List.ofFn node) (List.ofFn value)) = .ok (indices.map term) := by
    rw [range_eq, List.mapM_map, show interpolationTerm invert (List.ofFn node) (List.ofFn value) ∘
      Fin.val = (fun i ↦ Except.ok (term i)) from funext runs]
    exact List.mapM_pure
  refine ⟨(indices.map term).foldl add [], ?_, ?_⟩
  · simp [interpolateAt, List.length_ofFn, traversal, bind, Except.bind, pure, Except.pure]
  · rw [polynomial_sum, ofCoeffList_nil, zero_add, List.map_map, Lagrange.interpolate_apply]
    have enumerates : indices.toFinset = Finset.univ := by ext; simp [indices]
    rw [← enumerates, List.sum_toFinset _ (List.nodup_finRange n)]
    exact congrArg List.sum (List.map_congr_left fun i _ ↦ by simpa [enumerates] using represents i)

theorem interpolate_at_nodes (model : FieldModel) (d : String) (values nodes cs : List (model.Field d))
    (shift : model.Field d) (selected : points model d shift values.length = .ok nodes)
    (run : @interpolateAt _ _ ⟨0⟩ (inverse model d) nodes values = .ok cs) :
    interpolate model d values shift = .ok cs := by
  unfold interpolate
  rw [selected]
  exact run

/-- The checked primitive packages exactly the interpolator's coefficients. -/
theorem checked_interpolation (model : FieldModel) (d base : String) (values cs : List (model.Field d))
    (shift : model.Field d) (small : values.length < indexLimit)
    (runs : interpolate model d values shift = .ok cs) :
    checkedEvaluateOn model d base .polyInterpolate (.cons values (.cons shift .nil)) =
      .returned (.cons (PolynomialValue.ofCoefficients 0 cs) .nil) := by
  have checked : @checkValues model (Numerical.polyInterpolate.arguments d base)
      (.cons values (.cons shift .nil)) = .ok () := by
    change (do size values.length; Except.ok (); Except.ok ()) = _
    simp [size, small, bind, Except.bind]
  unfold checkedEvaluateOn
  rw [checked]
  change finish (do
    let cs ← interpolate model d values shift
    return Values.cons (Value := model.Value) (ty := Ty.polynomial d) (PolynomialValue.ofCoefficients 0 cs) .nil) = _
  rw [runs]
  rfl

theorem checked_coefficients (model : FieldModel) (d base : String) (p : PolynomialValue (model.Field d))
    (small : p.coefficients.length < indexLimit) (zero : p.zero = 0) :
    checkedEvaluateOn model d base .polyCoefficients (.cons p .nil) =
      .returned (.cons p.coefficients .nil) := by
  have checked : @checkValues model (Numerical.polyCoefficients.arguments d base) (.cons p .nil) = .ok () := by
    change (do (do size p.coefficients.length; require (p.zero = 0)); Except.ok ()) = _
    simp [size, small, require, zero, bind, Except.bind]
  unfold checkedEvaluateOn
  rw [checked]
  rfl

end Zkc.Source.Structured.Numerical
