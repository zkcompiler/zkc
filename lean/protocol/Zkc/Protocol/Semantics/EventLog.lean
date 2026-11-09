module

public import Mathlib.Data.List.OfFn
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Finite event logs over an arbitrary measurable event space.

The measurable structure is transported from the countable disjoint union of finite products.
Countable event spaces inherit discreteness from measurable singletons through Mathlib.
-/

public section

set_option autoImplicit false

open MeasureTheory

private theorem measurableEmbedding_sigmaMk {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (i : ι) : MeasurableEmbedding (Sigma.mk i : X i → Σ j, X j) where
  injective := sigma_mk_injective
  measurable := Measurable.of_le_map (iInf_le _ i)
  measurableSet_image' := by
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro j
    change MeasurableSet (Sigma.mk j ⁻¹' (Sigma.mk i '' s))
    by_cases h : j = i
    · subst j
      simpa only [sigma_mk_injective.preimage_image] using hs
    · have empty : Sigma.mk j ⁻¹' (Sigma.mk i '' s) = ∅ := by
        ext x
        constructor
        · rintro ⟨y, _, hy⟩
          exact (h (congrArg Sigma.fst hy).symm).elim
        · simp
      rw [empty]
      exact MeasurableSet.empty

namespace List

variable {L K X : Type*} [MeasurableSpace L] [MeasurableSpace K] [MeasurableSpace X]

/-- The disjoint union of finite product measurable spaces, indexed by list length. -/
instance instMeasurableSpace : MeasurableSpace (List L) :=
  MeasurableSpace.comap equivSigmaTuple inferInstance

/-- The canonical representation of a measurable list by its length and entries. -/
@[expose] def measurableEquivSigmaTuple : List L ≃ᵐ Σ n, Fin n → L where
  toEquiv := equivSigmaTuple
  measurable_toFun := comap_measurable _
  measurable_invFun := measurable_comap_iff.mpr (by
    simpa only [Equiv.self_comp_symm] using
      (measurable_id : Measurable (id : (Σ n, Fin n → L) → _)))

/-- A fixed-length tuple is measurably embedded as its list of entries. -/
theorem measurableEmbedding_ofFn (n : ℕ) : MeasurableEmbedding (ofFn : (Fin n → L) → List L) :=
  measurableEquivSigmaTuple.symm.measurableEmbedding.comp (measurableEmbedding_sigmaMk n)

theorem measurable_ofFn (n : ℕ) : Measurable (ofFn : (Fin n → L) → List L) :=
  (measurableEmbedding_ofFn n).measurable

instance instMeasurableSingletonClass [MeasurableSingletonClass L] :
    MeasurableSingletonClass (List L) where
  measurableSet_singleton xs := by
    simpa only [Set.image_singleton, ofFn_get] using
      (measurableEmbedding_ofFn xs.length).measurableSet_image' (measurableSet_singleton xs.get)

/-- Joint measurability can be checked separately on each pair of list lengths. -/
theorem measurable_prod_iff {f : List L × List K → X} :
    Measurable f ↔ ∀ n m, Measurable (fun p : (Fin n → L) × (Fin m → K) ↦
      f (ofFn p.1, ofFn p.2)) := by
  constructor
  · intro hf n m
    exact hf.comp ((measurable_ofFn n).prodMap (measurable_ofFn m))
  · intro hf s hs
    have cover : f ⁻¹' s = ⋃ n, ⋃ m,
        (Prod.map ofFn ofFn : (Fin n → L) × (Fin m → K) → List L × List K) ''
          ((fun p ↦ f (ofFn p.1, ofFn p.2)) ⁻¹' s) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
      constructor
      · intro hp
        exact ⟨p.1.length, p.2.length, (p.1.get, p.2.get), by simpa, by simp⟩
      · rintro ⟨n, m, q, hq, rfl⟩
        exact hq
    rw [cover]
    exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun m ↦
      ((measurableEmbedding_ofFn n).prodMap (measurableEmbedding_ofFn m)).measurableSet_image'
        (hf n m hs)

/-- Concatenation preserves measurability without a countability assumption on events. -/
theorem measurable_append : Measurable (fun p : List L × List L ↦ p.1 ++ p.2) := by
  apply measurable_prod_iff.mpr
  intro n m
  simp only [← ofFn_fin_append]
  apply (measurable_ofFn (n + m)).comp
  apply measurable_pi_iff.mpr
  intro i
  induction i using Fin.addCases with
  | left i =>
    simpa only [Fin.append_left, Function.comp_def] using
      (measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst :
        (Fin n → L) × (Fin m → L) → _))
  | right i =>
    simpa only [Fin.append_right, Function.comp_def] using
      (measurable_pi_apply i).comp (measurable_snd : Measurable (Prod.snd :
        (Fin n → L) × (Fin m → L) → _))

instance instMeasurableEq [MeasurableEq L] : MeasurableEq (List L) where
  measurableSet_diagonal := by
    apply measurableSet_setOfPred.mpr
    apply measurable_prod_iff.mpr
    intro n m
    by_cases h : n = m
    · subst m
      have entries : Measurable (fun p : (Fin n → L) × (Fin n → L) ↦ ∀ i, p.1 i = p.2 i) :=
        Measurable.forall fun i ↦
          ((measurable_pi_apply i).comp measurable_fst).eq
            ((measurable_pi_apply i).comp measurable_snd)
      simpa only [Set.diagonal, Set.mem_ofPred_eq, ofFn_inj, funext_iff] using entries
    · have unequal (p : (Fin n → L) × (Fin m → L)) : ofFn p.1 ≠ ofFn p.2 := by
        intro heq
        exact h (by simpa only [length_ofFn] using congrArg length heq)
      simpa only [Set.diagonal, Set.mem_ofPred_eq, unequal] using
        (measurable_const : Measurable (fun _ : (Fin n → L) × (Fin m → L) ↦ False))

end List
