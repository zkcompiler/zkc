module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
The uniform draw of a vector, and the weight of the zeros of a linear form.

`drawVector F n` is the uniform draw of a sequence of `n` elements of `F`: one uniform draw of
a function on `Fin n`, read as a list. The probability of a set of sequences under it is the
probability of the functions whose list is in the set, which is a count.

A linear form with a coefficient that is not zero vanishes on a uniform vector with probability
at most `1 / |F|` (`prEvent_linear_form_zero`, and `prEvent_drawVector_le_of_linear_form` for
the sequence that `drawVector` gives): the zeros of the form, each with any value at the
coordinate of that coefficient, are different vectors. This is the weight that a check by a
random linear combination pays for: Freivalds' check of a product, a batched equality.
-/

namespace ZkcFormal.Written
open OracleComp ProbComp
open scoped ENNReal

/-- The uniform draw of a sequence of `n` elements. -/
noncomputable def drawVector (F : Type) [SampleableType F] (n : ℕ) : ProbComp (List F) :=
  (fun v : Fin n → F => List.ofFn v) <$> ($ᵗ (Fin n → F))

section
variable {F : Type} [SampleableType F]

/-- What the draw of a sequence gives has its length. -/
theorem length_of_mem_support_drawVector (n : ℕ) (v : List F)
    (drawn : v ∈ support (drawVector F n)) : v.length = n := by
  simp only [drawVector, support_map, Set.mem_image] at drawn
  obtain ⟨w, _, rfl⟩ := drawn
  exact List.length_ofFn

/-- A set of sequences has the probability of the functions whose list is in it. -/
theorem prEvent_drawVector (n : ℕ) (p : List F → Prop) :
    Pr{let v ← drawVector F n}[p v] = Pr{let w ← $ᵗ (Fin n → F)}[p (List.ofFn w)] := by
  rw [drawVector, prEvent_map]

end

section
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The vectors on which a linear form vanishes. -/
def zerosOf {n : ℕ} (d : Fin n → F) : Finset (Fin n → F) :=
  Finset.univ.filter fun v => ∑ i, d i * v i = 0

/-- The zeros of a linear form with a coefficient that is not zero, each with any value at the
coordinate of that coefficient, are different vectors: there are at most `|F| ^ n / |F|` of
them. -/
theorem card_zerosOf_mul_le {n : ℕ} (d : Fin n → F) (j : Fin n) (nonzero : d j ≠ 0) :
    (zerosOf d).card * Fintype.card F ≤ Fintype.card F ^ n := by
  have injective : Set.InjOn (fun p : (Fin n → F) × F => Function.update p.1 j p.2)
      ((zerosOf d ×ˢ (Finset.univ : Finset F) : Finset ((Fin n → F) × F)) :
        Set ((Fin n → F) × F)) := by
    rintro ⟨v, t⟩ hv ⟨w, u⟩ hw same
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, zerosOf, Finset.mem_filter,
      Finset.mem_univ, true_and, and_true] at hv hw
    have tu : t = u := by simpa using congrFun same j
    have outside : ∀ i, i ≠ j → v i = w i := fun i ne => by
      simpa [Function.update_of_ne ne] using congrFun same i
    have atJ : d j * v j = d j * w j := by
      have split := fun (x : Fin n → F) =>
        Finset.add_sum_erase Finset.univ (fun i => d i * x i) (Finset.mem_univ j)
      have rest : ∑ i ∈ Finset.univ.erase j, d i * v i = ∑ i ∈ Finset.univ.erase j, d i * w i :=
        Finset.sum_congr rfl fun i hi => by rw [outside i (Finset.ne_of_mem_erase hi)]
      have hv' := hv
      rw [← split v] at hv'
      have hw' := hw
      rw [← split w] at hw'
      linear_combination hv' - hw' - rest
    have vw : v = w := funext fun i => by
      by_cases at_ : i = j
      · subst at_; exact mul_left_cancel₀ nonzero atJ
      · exact outside i at_
    simp [vw, tu]
  have bound := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) injective
  simpa [Finset.card_product, Fintype.card_fun] using bound

variable [SampleableType F]

/-- **A linear form that is not zero vanishes on a uniform vector with probability at most
`1 / |F|`.** -/
theorem prEvent_linear_form_zero {n : ℕ} (d : Fin n → F) (j : Fin n) (nonzero : d j ≠ 0) :
    Pr{let v ← $ᵗ (Fin n → F)}[∑ i, d i * v i = 0] ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample]
  have card : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (Or.inl card) (Or.inl (by simp))]
  have bound := card_zerosOf_mul_le d j nonzero
  simp only [zerosOf] at bound
  have total : Fintype.card (Fin n → F) = Fintype.card F ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [one_mul, total]
  exact_mod_cast bound

/-- The same of the sequence that `drawVector` gives: a set of sequences on each of which a
linear form that is not zero vanishes has at most `1 / |F|` of the draw. -/
theorem prEvent_drawVector_le_of_linear_form {n : ℕ} (p : List F → Prop) (d : Fin n → F)
    (j : Fin n) (nonzero : d j ≠ 0)
    (vanishes : ∀ w : Fin n → F, p (List.ofFn w) → ∑ i, d i * w i = 0) :
    Pr{let v ← drawVector F n}[p v] ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  rw [prEvent_drawVector]
  exact (prEvent_mono _ _ _ fun w holds => vanishes w holds).trans
    (prEvent_linear_form_zero d j nonzero)

end

end ZkcFormal.Written
