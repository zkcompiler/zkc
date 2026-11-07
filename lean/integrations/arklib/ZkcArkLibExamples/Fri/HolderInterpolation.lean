module

public import ZkcArkLibExamples.Fri.HolderFold
public import Zkc.Source.Structured.NumericalInterpolation
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! Interpolation at the retained holder's terminal coset. The installed
root table and inverse select the nodes. The mathematics determines the
normalized coefficients that the actual helper returns. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.HolderInterpolation
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model inverse_octic octicIdentity)
open ZkcSecurity.Domains.KoalaBear (Octic)
open FriSourceBodies FriSourceViews

private theorem ordered_nodes {A : Type} {n : Nat} (f : Nat → A) (node : Fin n → A)
    (evaluates : ∀ i : Fin n, node i = f i.val) : (List.range n).map f = List.ofFn node := by
  apply List.ext_getElem (by simp)
  intro j _ h
  simpa using (evaluates ⟨j, by simpa using h⟩).symm

private theorem nodes_eq {k : Nat} (bound : k ≤ 5) (shift : Octic) (nonzero : shift ≠ 0)
    (domain : Domain.SmoothCosetFftDomain k Octic)
    (geometry : ∀ j, domain j = point RetainedDomain.root shift k j) :
    Numerical.points model.toFieldModel octicIdentity shift (2 ^ k) = .ok (List.ofFn (fun j : Fin (2 ^ k) ↦ domain j)) := by
  rw [Numerical.points_eq _ _ _ _ _ (RetainedDomain.domainRoot k bound) nonzero]
  apply congrArg Except.ok
  exact ordered_nodes (fun i ↦ shift * RetainedDomain.root k ^ i) (fun j : Fin (2 ^ k) ↦ domain j) geometry

set_option maxRecDepth 4096 in
/-- Every polynomial below the terminal coset size is recovered by the
actual partial algorithm; the polynomial and the source coefficient list have
the same ascending coefficients after removing trailing zeros. -/
theorem interpolate_polynomial {k : Nat} (bound : k ≤ 5) (shift : Octic) (nonzero : shift ≠ 0)
    (domain : Domain.SmoothCosetFftDomain k Octic)
    (geometry : ∀ j, domain j = point RetainedDomain.root shift k j)
    (word : Fin (2 ^ k) → Octic) (p : Polynomial Octic)
    (degree : p.degree < (2 ^ k : Nat)) (represented : ∀ i, p.eval (domain i) = word i) :
    ∃ cs : List Octic, Numerical.interpolate model.toFieldModel octicIdentity (List.ofFn word) shift = .ok cs ∧
      Polynomial.ofCoeffList cs = p := by
  let _ : Inhabited Octic := ⟨0⟩
  let invert : Octic → Numerical.Result Octic := Numerical.inverse model.toFieldModel octicIdentity
  have inverts (x : Octic) (h : x ≠ 0) : invert x = .ok x⁻¹ :=
    Numerical.inverse_eq model.toFieldModel octicIdentity (fun y : Octic ↦ (y⁻¹ : Octic)) inverse_octic x h
  obtain ⟨cs, run, represents⟩ := Numerical.interpolateAt_spec (F := Octic) (fun j : Fin (2 ^ k) ↦ domain j) word domain.injective
    invert inverts
  refine ⟨cs, ?_, represents.trans ?_⟩
  · have points : Numerical.points model.toFieldModel octicIdentity shift (List.ofFn word).length =
        .ok (List.ofFn (fun i : Fin (2 ^ k) ↦ domain i)) :=
      (congrArg (Numerical.points model.toFieldModel octicIdentity shift)
        (List.length_ofFn (f := word))).trans (nodes_eq bound shift nonzero domain geometry)
    exact Numerical.interpolate_at_nodes model.toFieldModel octicIdentity _ _ cs shift points run
  · symm
    apply Lagrange.eq_interpolate_of_eval_eq _ domain.injective.injOn
    · simpa using degree
    · exact fun i _ ↦ represented i

abbrev interpolation : Primitive := .numerical .polyInterpolate octicIdentity ""
abbrev coefficients : Primitive := .numerical .polyCoefficients octicIdentity ""

private def interpolateLaw := ReferenceLibrary.marked model "s2"
  (ReferenceLibrary.execute model (inputs := helper17Helper.inputs) interpolation
    (.cons .here (.cons (.there .here) .nil)))

private def coefficientLaw := ReferenceLibrary.marked model "s0"
  (ReferenceLibrary.execute model (inputs := helper18Helper.inputs) coefficients (.cons .here .nil))

/-- The linked interpolation helper, on a terminal word of degree below one,
returns the source representation of the word's unique constant. -/
theorem installed_constant {I : PIR.Signature} {k : Nat} (bound : k ≤ 5)
    (shift : Octic) (nonzero : shift ≠ 0) (domain : Domain.SmoothCosetFftDomain k Octic)
    (geometry : ∀ j, domain j = point RetainedDomain.root shift k j) (c : Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper17Helper
      (.cons (List.ofFn (fun _ : Fin (2 ^ k) ↦ c)) (.cons shift .nil)) =
        .done (.cons (PolynomialValue.ofCoefficients 0 [c]) .nil) := by
  have degree : (Polynomial.C c).degree < (2 ^ k : Nat) := by
    apply lt_of_le_of_lt Polynomial.degree_C_le
    exact_mod_cast (Nat.two_pow_pos k)
  obtain ⟨cs, runs, represents⟩ := interpolate_polynomial bound shift nonzero domain geometry
    (fun _ ↦ c) (Polynomial.C c) degree (fun _ ↦ Polynomial.eval_C)
  have same : PolynomialValue.ofCoefficients 0 cs = PolynomialValue.ofCoefficients 0 [c] := by
    have canonical := Numerical.normalized_eq_of_polynomial (F := Octic) cs [c]
      (represents.trans (by simp [Polynomial.ofCoeffList_cons]))
    unfold PolynomialValue.ofCoefficients
    congr 1
  have admissible : 2 ^ k < indexLimit :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) bound) (by decide : 2 ^ 5 < indexLimit)
  refine (interpolateLaw.invokeOn (I := I) unit.definitions unit.linked
    (helper := helper17Helper) (by exact_body helper17Definition) _ trivial).trans ?_
  change primitiveOutcome (Numerical.checkedEvaluateOn model.toFieldModel octicIdentity "" .polyInterpolate
    (.cons (List.ofFn (fun _ : Fin (2 ^ k) ↦ c)) (.cons shift .nil))) = _
  have size : (List.ofFn (fun _ : Fin (2 ^ k) ↦ c)).length < indexLimit :=
    List.length_ofFn.symm ▸ admissible
  refine (congrArg (@primitiveOutcome I _) (Numerical.checked_interpolation model.toFieldModel
    octicIdentity "" _ cs shift size runs)).trans ?_
  exact congrArg (fun p ↦ PIR.Process.done (I := I)
    (Values.cons (Value := model.Value) (ty := .polynomial octicIdentity) p .nil)) same

/-- Projecting the installed polynomial returns its exact canonical list. -/
theorem installed_coefficients {I : PIR.Signature} (c : Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper18Helper
        (.cons (PolynomialValue.ofCoefficients 0 [c]) .nil) =
      .done (.cons (normalizeCoefficients 0 [c]) .nil) := by
  refine (coefficientLaw.invokeOn (I := I) unit.definitions unit.linked
    (helper := helper18Helper) (by exact_body helper18Definition) _ trivial).trans ?_
  let value := PolynomialValue.ofCoefficients (0 : Octic) [c]
  have size : value.coefficients.length < indexLimit := lt_of_le_of_lt
    (normalizeCoefficients_length_le (0 : Octic) [c]) (show 1 < indexLimit by decide)
  change primitiveOutcome (Numerical.checkedEvaluateOn model.toFieldModel octicIdentity "" .polyCoefficients
    (.cons value .nil)) = _
  exact congrArg (@primitiveOutcome I _) (Numerical.checked_coefficients model.toFieldModel octicIdentity ""
    value size rfl)

/-- Degree below one forces the source terminal word to be constant. The two
actual helper invocations recover its complete canonical coefficients. -/
theorem installed_codeword {I : PIR.Signature} {k : Nat} (bound : k ≤ 5)
    (shift : Octic) (nonzero : shift ≠ 0) (domain : Domain.SmoothCosetFftDomain k Octic)
    (geometry : ∀ j, domain j = point RetainedDomain.root shift k j)
    (word : Fin (2 ^ k) → Octic)
    (codeword : word ∈ ReedSolomon.code (domain : Fin (2 ^ k) ↪ Octic) 1) :
    ∃ c : Octic, (∀ i, word i = c) ∧
      invoke (RetainedFold.helpers (I := I)).closed helper17Helper
          (.cons (List.ofFn word) (.cons shift .nil)) = .done (.cons (PolynomialValue.ofCoefficients 0 [c]) .nil) ∧
      invoke (RetainedFold.helpers (I := I)).closed helper18Helper
          (.cons (PolynomialValue.ofCoefficients 0 [c]) .nil) = .done (.cons (normalizeCoefficients 0 [c]) .nil) := by
  obtain ⟨p, degree, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero.mp codeword
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp (show p.natDegree = 0 by omega)
  have word_eq : ReedSolomon.evalOnPoints (domain : Fin (2 ^ k) ↪ Octic) (Polynomial.C c) = fun _ ↦ c := by
    funext i
    exact Polynomial.eval_C
  rw [word_eq]
  exact ⟨c, fun _ ↦ rfl, installed_constant bound shift nonzero domain geometry c, installed_coefficients c⟩

end ZkcSecurity.ArkLib.Fri.HolderInterpolation
