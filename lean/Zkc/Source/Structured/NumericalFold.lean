module

public import Zkc.Source.Structured.NumericalEvaluation

@[expose] public section

/-! Natural-order cells returned by the checked binary polynomial fold.
Each inverse is the one installed in the selected field model. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Numerical
local instance (model : FieldModel) (d : String) : Inhabited (model.Field d) := ⟨0⟩

theorem inverse_eq (model : FieldModel) (d : String) (inv : model.Field d → model.Field d)
    (supplied : model.inverse d = some inv) (x : model.Field d) (nonzero : x ≠ 0) :
    Numerical.inverse model d x = .ok (inv x) := by
  simp [Numerical.inverse, Numerical.require, supplied, nonzero]

theorem points_eq (model : FieldModel) (d : String) (n : Nat)
    (shift generator : model.Field d)
    (root : Numerical.domainRoot model d n = .ok generator) (nonzero : shift ≠ 0) :
    Numerical.points model d shift n =
      .ok ((List.range n).map (fun i ↦ shift * generator ^ i)) := by
  simp [Numerical.points, root, Numerical.require, nonzero, bind, Except.bind, pure, Except.pure]

/-- Successful element equations preserve every position of the existing monadic traversal. -/
private theorem mapM_ok {A B : Type} (xs : List A) (f : A → Numerical.Result B) (g : A → B)
    (returns : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have head := returns x (by simp)
    have tail := ih (fun a member ↦ returns a (by simp [member]))
    simp only [List.mapM_cons, head, tail, List.map_cons, bind, Except.bind, pure, Except.pure]

/-- The actual fold evaluator returns the ordered low/high pairing and its stored inverses. -/
theorem fold_cells (model : FieldModel) (d base : String) (xs : List (model.Field d))
    (shift beta generator : model.Field d) (inv : model.Field d → model.Field d)
    (root : Numerical.domainRoot model d xs.length = .ok generator) (nonzero : shift ≠ 0)
    (length : 2 ≤ xs.length) (supplied : model.inverse d = some inv)
    (two : (2 : model.Field d) ≠ 0)
    (points : ∀ i < xs.length / 2, shift * generator ^ i ≠ 0) :
    Numerical.evaluateOn model d base .polyFold (.cons xs (.cons shift (.cons beta .nil))) =
      .returned (.cons ((List.range (xs.length / 2)).map (fun i ↦
        (xs[i]! + xs[i + xs.length / 2]!) * inv 2 +
          beta * (xs[i]! - xs[i + xs.length / 2]!) * inv 2 *
            inv (shift * generator ^ i))) .nil) := by
  have domain := points_eq model d xs.length shift generator root nonzero
  have coordinate (i : Nat) (bound : i < xs.length / 2) :
      ((List.range xs.length).map (fun j ↦ shift * generator ^ j))[i]! =
        shift * generator ^ i := by
    have inside : i < xs.length := Nat.lt_of_lt_of_le bound (Nat.div_le_self _ _)
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range inside, Option.map_some, Option.getD_some]
  simp only [Numerical.evaluateOn, domain, Numerical.require, ite_eq_left length,
    inverse_eq model d inv supplied 2 two, bind, Except.bind, pure, Except.pure]
  have traversal := mapM_ok (List.range (xs.length / 2))
    (fun i ↦ do
      let inverseX ← Numerical.inverse model d
        (((List.range xs.length).map (fun j ↦ shift * generator ^ j))[i]!)
      pure ((xs[i]! + xs[i + xs.length / 2]!) * inv 2 +
        beta * (xs[i]! - xs[i + xs.length / 2]!) * inv 2 * inverseX))
    (fun i ↦ (xs[i]! + xs[i + xs.length / 2]!) * inv 2 +
      beta * (xs[i]! - xs[i + xs.length / 2]!) * inv 2 * inv (shift * generator ^ i)) (by
      intro i member
      have bound := List.mem_range.mp member
      rw [coordinate i bound, inverse_eq model d inv supplied _ (points i bound)]
      rfl)
  exact congrArg (fun result : Numerical.Result (List (model.Field d)) ↦
    Numerical.finish (do
      let values ← result
      pure (Values.cons values .nil : Values model.Value [.vector d]))) traversal

/-- Size admission is separate from root and inverse availability. -/
theorem checked_fold (model : FieldModel) (d base : String) (xs : List (model.Field d))
    (shift beta : model.Field d) (sizeBound : xs.length < indexLimit) :
    checkedEvaluateOn model d base .polyFold (.cons xs (.cons shift (.cons beta .nil))) =
      evaluateOn model d base .polyFold (.cons xs (.cons shift (.cons beta .nil))) := by
  unfold checkedEvaluateOn
  have admitted : @checkValues model (Numerical.polyFold.arguments d base)
      (.cons xs (.cons shift (.cons beta .nil))) = .ok () := by
    change (do size xs.length; Except.ok (); Except.ok (); Except.ok ()) = Except.ok ()
    simp [size, sizeBound, bind, Except.bind]
  rw [admitted]

end Zkc.Source.Structured.Numerical
