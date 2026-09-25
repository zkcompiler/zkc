import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Exact algebra of the denominator-free product fingerprint.

Two finite row families are connected when their selected values are equal as
multisets. That relation involves no challenge. Mathlib's
`Polynomial.ofMultiset s`, the product of `X - C a` over `s`, is the
fingerprint polynomial; over an integral domain it determines `s`. Distinct
multisets therefore have a nonzero fingerprint difference, and the challenges
at which their evaluations agree are roots of that difference.

A forward multiplicative prefix recurrence determines every accumulator value
from its initial value and factors. No step divides, so a zero factor constrains
all later values. Turning root counts into a probability, commitment order,
tuple-compression error and the soundness of the argument that checks the
recurrence are premises of a protocol theorem, not of these lemmas.
-/

set_option autoImplicit false

namespace Zkc.Algebra.MultisetFingerprint

open Polynomial

section Rows

variable {ι κ α β : Type}

/-- Values of the selected rows, counted with multiplicity. -/
def rowValues (selected : Finset ι) (value : ι → α) : Multiset α :=
  selected.val.map value

theorem rowValues_univ_of_equiv [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (left : ι → α) (right : κ → α) (agree : ∀ i, right (e i) = left i) :
    rowValues Finset.univ left = rowValues Finset.univ right := by
  rw [rowValues, rowValues, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => (agree i).symm

/-- Equality of all-row multisets is exactly the existence of a row bijection
that preserves values. -/
theorem rowValues_univ_eq_iff [Fintype ι] [Fintype κ] (left : ι → α) (right : κ → α) :
    rowValues Finset.univ left = rowValues Finset.univ right ↔
      ∃ e : ι ≃ κ, ∀ i, right (e i) = left i := by
  classical
  refine ⟨fun same => ?_, fun ⟨e, agree⟩ => rowValues_univ_of_equiv e left right agree⟩
  have fiber (x : α) :
      Fintype.card {i // left i = x} = Fintype.card {j // right j = x} := by
    have counts := congrArg (Multiset.count x) same
    simp only [rowValues, Multiset.count_map] at counts
    simpa [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm] using counts
  exact ⟨Equiv.ofFiberEquiv fun x => Fintype.equivOfCardEq (fiber x),
    Equiv.ofFiberEquiv_map _⟩

/-- Encoding values, for example compressing a row tuple into one field element,
trivially preserves equal multisets. Reflecting equality back needs injectivity
only on the values that actually occur. -/
theorem eq_of_map_eq_of_injOn (encode : α → β) {s t : Multiset α}
    (injective : Set.InjOn encode {x | x ∈ s ∨ x ∈ t})
    (encoded : s.map encode = t.map encode) : s = t := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact (Multiset.eq_zero_of_forall_notMem fun x => isEmptyElim x).trans
      (Multiset.eq_zero_of_forall_notMem fun x => isEmptyElim x).symm
  have decode (u : Multiset α) (occurs : ∀ x ∈ u, x ∈ s ∨ x ∈ t) :
      (u.map encode).map (Function.invFunOn encode {x | x ∈ s ∨ x ∈ t}) = u := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id u]
    exact Multiset.map_congr rfl fun x member =>
      injective.leftInvOn_invFunOn (occurs x member)
  calc s = (s.map encode).map (Function.invFunOn encode {x | x ∈ s ∨ x ∈ t}) :=
        (decode s fun _ member => Or.inl member).symm
    _ = (t.map encode).map (Function.invFunOn encode {x | x ∈ s ∨ x ∈ t}) := by rw [encoded]
    _ = t := decode t fun _ member => Or.inr member

end Rows

section Fingerprint

variable {ι : Type} {R : Type} [CommRing R]

theorem eval_ofMultiset (s : Multiset R) (z : R) :
    (ofMultiset s).eval z = (s.map fun a => z - a).prod := by
  simp [ofMultiset_apply, eval_multiset_prod, Multiset.map_map]

theorem eval_ofMultiset_rowValues (selected : Finset ι) (value : ι → R) (z : R) :
    (ofMultiset (rowValues selected value)).eval z = ∏ i ∈ selected, (z - value i) := by
  rw [eval_ofMultiset, rowValues, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

theorem ofMultiset_isMonicOfDegree [Nontrivial R] (s : Multiset R) :
    (ofMultiset s).IsMonicOfDegree (Multiset.card s) :=
  ⟨by simp [ofMultiset_apply],
    by simpa [ofMultiset_apply] using
      monic_multiset_prod_of_monic s (fun a => X - C a) fun a _ => monic_X_sub_C a⟩

/-- Over an integral domain the fingerprint polynomial is the multiset relation
itself; no evaluation point is involved. -/
theorem ofMultiset_eq_iff [IsDomain R] {s t : Multiset R} :
    ofMultiset s = ofMultiset t ↔ s = t :=
  (ofMultiset_injective R).eq_iff

theorem ofMultiset_rowValues_univ_eq_iff {κ : Type} [IsDomain R] [Fintype ι] [Fintype κ]
    (left : ι → R) (right : κ → R) :
    ofMultiset (rowValues Finset.univ left) = ofMultiset (rowValues Finset.univ right) ↔
      ∃ e : ι ≃ κ, ∀ i, right (e i) = left i :=
  ofMultiset_eq_iff.trans (rowValues_univ_eq_iff left right)

theorem ofMultiset_sub_ne_zero [IsDomain R] {s t : Multiset R} (distinct : s ≠ t) :
    ofMultiset s - ofMultiset t ≠ 0 :=
  sub_ne_zero.mpr ((ofMultiset_injective R).ne distinct)

theorem natDegree_ofMultiset_sub_le [Nontrivial R] (s t : Multiset R) :
    (ofMultiset s - ofMultiset t).natDegree ≤ max (Multiset.card s) (Multiset.card t) := by
  simpa [(ofMultiset_isMonicOfDegree s).natDegree_eq,
    (ofMultiset_isMonicOfDegree t).natDegree_eq] using
    natDegree_sub_le (ofMultiset s) (ofMultiset t)

/-- Equal cardinalities cancel the common leading term. -/
theorem natDegree_ofMultiset_sub_lt [Nontrivial R] {s t : Multiset R}
    (sameCard : Multiset.card s = Multiset.card t) (nonempty : s ≠ 0) :
    (ofMultiset s - ofMultiset t).natDegree < Multiset.card s :=
  (ofMultiset_isMonicOfDegree s).natDegree_sub_lt
    (Multiset.card_eq_zero.not.mpr nonempty) (sameCard ▸ ofMultiset_isMonicOfDegree t)

/-- Challenges at which distinct fingerprints agree are roots of their nonzero
difference, whatever else those challenges were used for. -/
theorem agreeing_card_le_natDegree [IsDomain R] {s t : Multiset R} (distinct : s ≠ t)
    (points : Finset R)
    (agree : ∀ z ∈ points, (ofMultiset s).eval z = (ofMultiset t).eval z) :
    points.card ≤ (ofMultiset s - ofMultiset t).natDegree := by
  apply card_le_degree_of_subset_roots
  intro z member
  rw [mem_roots (ofMultiset_sub_ne_zero distinct), IsRoot, eval_sub, sub_eq_zero]
  exact agree z member

/-- The exact count behind a collision bound. A probability additionally needs a
uniform challenge that is independent of both multisets. -/
theorem agreeing_card_le [IsDomain R] {s t : Multiset R} (distinct : s ≠ t)
    (points : Finset R)
    (agree : ∀ z ∈ points, (ofMultiset s).eval z = (ofMultiset t).eval z) :
    points.card ≤ max (Multiset.card s) (Multiset.card t) :=
  (agreeing_card_le_natDegree distinct points agree).trans (natDegree_ofMultiset_sub_le s t)

theorem agreeing_card_lt [IsDomain R] {s t : Multiset R} (distinct : s ≠ t)
    (sameCard : Multiset.card s = Multiset.card t) (points : Finset R)
    (agree : ∀ z ∈ points, (ofMultiset s).eval z = (ofMultiset t).eval z) :
    points.card < Multiset.card s := by
  refine (agreeing_card_le_natDegree distinct points agree).trans_lt
    (natDegree_ofMultiset_sub_lt sameCard ?_)
  rintro rfl
  exact distinct (Multiset.card_eq_zero.mp sameCard.symm).symm

end Fingerprint

section Recurrence

variable {M : Type} [CommMonoid M]

/-- A witness obeying the forward multiplicative recurrence is its initial value
times the ordered prefix product, at every row up to the bound. -/
theorem recurrence_eq_prefix_prod (factor state : ℕ → M) (n : ℕ)
    (step : ∀ i < n, state (i + 1) = state i * factor i) :
    ∀ k ≤ n, state k = state 0 * ∏ i ∈ Finset.range k, factor i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k previous =>
      intro bound
      rw [step k bound, previous (Nat.le_of_succ_le bound), Finset.prod_range_succ, mul_assoc]

variable {K : Type} [CommRing K]

/-- Any accumulator starting at one and multiplying by `z - value i` ends at the
fingerprint evaluation, including when some factor is zero. -/
theorem recurrence_eq_eval (value : ℕ → K) (z : K) (state : ℕ → K) (n : ℕ)
    (start : state 0 = 1) (step : ∀ i < n, state (i + 1) = state i * (z - value i)) :
    state n = (ofMultiset (rowValues (Finset.range n) value)).eval z := by
  rw [eval_ofMultiset_rowValues, recurrence_eq_prefix_prod _ state n step n le_rfl, start,
    one_mul]

/-- Unselected rows, such as padding, contribute factor one and are absent from
the multiset. -/
theorem selected_recurrence_eq_eval (selected : ℕ → Prop) [DecidablePred selected]
    (value : ℕ → K) (z : K) (state : ℕ → K) (n : ℕ) (start : state 0 = 1)
    (step : ∀ i < n, state (i + 1) = state i * if selected i then z - value i else 1) :
    state n =
      (ofMultiset (rowValues ((Finset.range n).filter selected) value)).eval z := by
  rw [eval_ofMultiset_rowValues, Finset.prod_filter,
    recurrence_eq_prefix_prod _ state n step n le_rfl, start, one_mul]

end Recurrence

end Zkc.Algebra.MultisetFingerprint
