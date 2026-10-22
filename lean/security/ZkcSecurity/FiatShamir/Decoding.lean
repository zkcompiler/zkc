module

public import ZkcSecurity.FiatShamir.Sampling
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

@[expose] public section

/-! Field challenges decoded from wide uniform samples.

A transcript suite derives a field challenge by squeezing a fixed number of
bytes and reducing their integer modulo the field size. The reduced sample is
close to, not exactly, uniform. `balanced_of_fibers` bounds the excess of every
event by `|F| / |B|` when no field element has more than `|B| / |F| + 1` of the
samples; `balanced_reduce` applies it to reduction modulo the field size of a
uniform integer below `N`, through a numbering of the field elements. Combined
with `adaptive_soundness`, a suite that squeezes `k` bytes adds `|F| / 2^(8k)`
to the per-challenge error.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp

variable {F B : Type}

/-- If every fiber of `decode` has at most `fiber` samples, and `fiber` is at most
`|B| / |F| + 1`, every event of the decoded sample is at most `|F| / |B|`
likelier than under the uniform field. -/
theorem balanced_of_fibers [Fintype F] [Fintype B] [SampleableType F] [SampleableType B]
    [DecidableEq F] (decode : B → F) (fiber : ℕ)
    (small : ∀ challenge, (Finset.univ.filter fun answer => decode answer = challenge).card ≤ fiber)
    (covering : fiber * Fintype.card F ≤ Fintype.card B + Fintype.card F) :
    Balanced decode ((Fintype.card F : ENNReal) / Fintype.card B) := by
  intro event
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample]
  set events := Finset.univ.filter event
  set hits := Finset.univ.filter fun answer => event (decode answer)
  have counted : hits.card ≤ events.card * fiber := by
    have partitioned : hits.card =
        ∑ challenge ∈ events, (hits.filter fun answer => decode answer = challenge).card :=
      Finset.card_eq_sum_card_fiberwise (fun answer member => by simpa [hits, events] using member)
    rw [partitioned]
    calc ∑ challenge ∈ events, (hits.filter fun answer => decode answer = challenge).card
        ≤ ∑ _challenge ∈ events, fiber := Finset.sum_le_sum fun challenge _ =>
          (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
            (small challenge)
      _ = events.card * fiber := by simp
  have bounded : events.card ≤ Fintype.card F := Finset.card_le_univ _
  have numerators : hits.card * Fintype.card F ≤
      events.card * Fintype.card B + Fintype.card F * Fintype.card F := by
    calc hits.card * Fintype.card F ≤ events.card * fiber * Fintype.card F :=
          Nat.mul_le_mul_right _ counted
      _ = events.card * (fiber * Fintype.card F) := Nat.mul_assoc _ _ _
      _ ≤ events.card * (Fintype.card B + Fintype.card F) := Nat.mul_le_mul_left _ covering
      _ = events.card * Fintype.card B + events.card * Fintype.card F := Nat.mul_add _ _ _
      _ ≤ events.card * Fintype.card B + Fintype.card F * Fintype.card F :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ bounded) _
  have fieldPositive : (Fintype.card F : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  have samplePositive : (Fintype.card B : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := B)).ne'
  have common : ((events.card * Fintype.card B + Fintype.card F * Fintype.card F : ℕ) :
      ENNReal) / (Fintype.card F * Fintype.card B : ℕ) =
        (events.card : ENNReal) / Fintype.card F + (Fintype.card F : ENNReal) / Fintype.card B := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ENNReal.add_div,
      ENNReal.mul_div_mul_right _ _ samplePositive (ENNReal.natCast_ne_top _),
      ENNReal.mul_div_mul_left _ _ fieldPositive (ENNReal.natCast_ne_top _)]
  rw [← common]
  calc (hits.card : ENNReal) / Fintype.card B
      = ((hits.card * Fintype.card F : ℕ) : ENNReal) / (Fintype.card F * Fintype.card B : ℕ) := by
        rw [Nat.cast_mul, Nat.cast_mul, mul_comm (Fintype.card F : ENNReal) (Fintype.card B),
          ENNReal.mul_div_mul_right _ _ fieldPositive (ENNReal.natCast_ne_top _)]
    _ ≤ ((events.card * Fintype.card B + Fintype.card F * Fintype.card F : ℕ) : ENNReal) /
          (Fintype.card F * Fintype.card B : ℕ) := by
        gcongr

/-- Reduction of a sample below `N` modulo the field size, read through a
numbering of the field elements. -/
def reduce [Fintype F] [Nonempty F] (numbering : F ≃ Fin (Fintype.card F)) (N : ℕ)
    (sample : Fin N) : F :=
  numbering.symm ⟨sample.val % Fintype.card F, Nat.mod_lt _ Fintype.card_pos⟩

/-- At most `N / |F| + 1` samples below `N` reduce to each field element. -/
theorem reduce_fiber [Fintype F] [Nonempty F] [DecidableEq F]
    (numbering : F ≃ Fin (Fintype.card F)) (N : ℕ) (challenge : F) :
    (Finset.univ.filter fun sample : Fin N => reduce numbering N sample = challenge).card ≤
      N / Fintype.card F + 1 := by
  have injective : Set.InjOn (fun sample : Fin N => sample.val / Fintype.card F)
      (Finset.univ.filter fun sample : Fin N => reduce numbering N sample = challenge) := by
    intro first firstMember second secondMember same
    rw [Finset.coe_filter] at firstMember secondMember
    have firstReduced : reduce numbering N first = challenge := by simpa using firstMember
    have secondReduced : reduce numbering N second = challenge := by simpa using secondMember
    have residues : first.val % Fintype.card F = second.val % Fintype.card F := by
      have := congrArg (fun value => (numbering value).val) (firstReduced.trans secondReduced.symm)
      simpa [reduce] using this
    apply Fin.ext
    rw [← Nat.div_add_mod first.val (Fintype.card F),
      ← Nat.div_add_mod second.val (Fintype.card F), residues]
    simp only at same
    rw [same]
  calc (Finset.univ.filter fun sample : Fin N => reduce numbering N sample = challenge).card
      ≤ (Finset.range (N / Fintype.card F + 1)).card := by
        apply Finset.card_le_card_of_injOn _ _ injective
        intro sample _
        simp only [Finset.coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right sample.isLt.le)
    _ = N / Fintype.card F + 1 := Finset.card_range _

/-- Reducing a uniform sample below `N` modulo the field size adds at most
`|F| / N` to every event of a uniform field challenge. -/
theorem balanced_reduce [Fintype F] [Nonempty F] [DecidableEq F] [SampleableType F]
    (numbering : F ≃ Fin (Fintype.card F)) (N : ℕ) [NeZero N] [SampleableType (Fin N)] :
    Balanced (reduce numbering N) ((Fintype.card F : ENNReal) / N) := by
  have balanced := balanced_of_fibers (reduce numbering N) (N / Fintype.card F + 1)
    (reduce_fiber numbering N) (by
      rw [Fintype.card_fin, Nat.add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self N _) _)
  simpa only [Fintype.card_fin] using balanced

/-- Reducing a uniform sample below `N` modulo the field size multiplies every
event's probability by at most `1 + |F| / N`. -/
theorem dominated_reduce [Fintype F] [Nonempty F] [DecidableEq F] [SampleableType F]
    (numbering : F ≃ Fin (Fintype.card F)) (N : ℕ) [NeZero N] [SampleableType (Fin N)] :
    Dominated (reduce numbering N) (1 + (Fintype.card F : ENNReal) / N) := by
  have bounded := pointBound_of_fibers (reduce numbering N) _ (reduce_fiber numbering N)
  rw [Fintype.card_fin] at bounded
  refine bounded.dominated.mono ?_
  have nonzero : (N : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
  calc ((N / Fintype.card F + 1 : ℕ) : ENNReal) / N * Fintype.card F
      = (((N / Fintype.card F + 1) * Fintype.card F : ℕ) : ENNReal) / N := by
        rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, Nat.cast_mul]
    _ ≤ ((N + Fintype.card F : ℕ) : ENNReal) / N := by
        gcongr
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_right (Nat.div_mul_le_self N _) _
    _ = 1 + (Fintype.card F : ENNReal) / N := by
        rw [Nat.cast_add, ENNReal.add_div, ENNReal.div_self nonzero (ENNReal.natCast_ne_top _)]

/-- A balanced total decoding is realized with factor one and its loss as
slack. -/
theorem Balanced.realized [SampleableType F] [SampleableType B] {decode : B → F}
    {loss : ENNReal} (balanced : Balanced decode loss) :
    Realized (fun answer => some (decode answer)) 1 loss := by
  intro event
  rw [one_mul, prEvent_congr _ _ (fun answer => event (decode answer)) fun answer =>
    ⟨fun ⟨_, decoded, holds⟩ => by
        cases Option.some.inj decoded
        exact holds,
      fun holds => ⟨_, rfl, holds⟩⟩]
  exact balanced event

end ZkcSecurity.FiatShamir
