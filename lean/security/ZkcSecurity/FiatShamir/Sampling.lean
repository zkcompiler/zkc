module

public import ZkcSecurity.FiatShamir.Typed
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.BLS12_381.Basic

@[expose] public section

/-! Sampling corrections of decoded query sites.

A query site decodes a uniform oracle answer into its result sort, and the
certificate of `ZkcSecurity.FiatShamir.Typed` bounds escapes under this decoded
law. A protocol's round-by-round analysis bounds escapes under the uniform law
of the sort instead. This module relates the two through additive and multiplicative bounds.

- `Dominated decode factor`: every event of the decoded value is at most
  `factor` times as likely as the same event of a uniform value of the sort. A
  site whose escape set has uniform probability at most `ε` then escapes under
  the decoded law with probability at most `factor * ε` (`Dominated.escape_le`).
- `PointBound decode bound`: every value has decoded probability at most
  `bound`. With `bound = (1 + η) / |R|` the factor is `1 + η`
  (`PointBound.dominated`). Fiber counts give point bounds
  (`pointBound_of_fibers`).
- Exact sampling: a bijective decoding is dominated with factor one
  (`dominated_of_bijective`), and so is reducing a uniform sample modulo a
  divisor of its range (`modulo_exact`). Binary-field challenges read from
  machine words and power-of-two windows of uniform bit strings are of this
  kind; their sites keep their uniform-law errors with no correction.
- Low bits: `lowBits p bits` masks the canonical representative of a residue
  modulo `p`, which is how a transcript derives a `bits`-bit index or a
  proof-of-work test from a squeezed prime-field element. Each value has at
  most `⌈p / 2 ^ bits⌉` preimages (`lowBits_pointBound`). For KoalaBear,
  `p = 127 · 2 ^ 24 + 1`, so for `bits ≤ 24` the factor is
  `1 + (2 ^ bits - 1) / p` (`koalaBear_lowBits_dominated`): `1 + 65535 / p` at
  16 bits and `1 + 2097151 / p` at 21 bits.
- Independent coordinates of a uniform answer multiply point bounds
  (`PointBound.prod`, `PointBound.pi`), so a compound draw of `s` values each
  with factor `1 + η` has factor `(1 + η) ^ s`.

A multiplicative factor scales with the event. An additive loss (`Balanced`)
does not: the same 16-bit KoalaBear sample has additive loss
`65535 / (p · 2 ^ 16)`, about `2 ^ -31`, which dominates any round error
below it, whereas the factor `1 + 65535 / p` costs about `2 ^ -14.99` relative
to the round error.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp

section Additive
variable {F B : Type} [SampleableType F]

/-- Decoded oracle answers: every event of the decoded challenge is at most
`loss` likelier than under the uniform field. -/
def Balanced [SampleableType B] (decode : B → F) (loss : ENNReal) : Prop :=
  ∀ event : F → Prop,
    Pr{let answer ← $ᵗ B}[event (decode answer)] ≤ Pr{let challenge ← $ᵗ F}[event challenge] + loss

theorem balanced_id : Balanced (B := F) (id : F → F) 0 := fun _ => by simp

end Additive

section Laws
variable {B R : Type}

/-- Every value of the decoded answer has probability at most `bound`. -/
def PointBound [SampleableType B] (decode : B → R) (bound : ENNReal) : Prop :=
  ∀ value, Pr{let answer ← $ᵗ B}[decode answer = value] ≤ bound

/-- Every event of the decoded answer is at most `factor` times as likely as the
same event of a uniform value of the sort. -/
def Dominated [SampleableType B] [SampleableType R] (decode : B → R) (factor : ENNReal) :
    Prop :=
  ∀ event : R → Prop,
    Pr{let answer ← $ᵗ B}[event (decode answer)] ≤ factor * Pr{let value ← $ᵗ R}[event value]

variable [SampleableType B] [SampleableType R]

/-- A site whose escape set has uniform probability at most `error` escapes
under a dominated decoding with probability at most `factor * error`. -/
theorem Dominated.escape_le {decode : B → R} {factor : ENNReal}
    (dominated : Dominated decode factor) (event : R → Prop) {error : ENNReal}
    (bounded : Pr{let value ← $ᵗ R}[event value] ≤ error) :
    Pr{let answer ← $ᵗ B}[event (decode answer)] ≤ factor * error :=
  (dominated event).trans (by gcongr)

theorem Dominated.mono {decode : B → R} {factor larger : ENNReal}
    (dominated : Dominated decode factor) (le : factor ≤ larger) : Dominated decode larger :=
  fun event => (dominated event).trans (by gcongr)

/-- The undecoded uniform answer is exact. -/
theorem dominated_id : Dominated (id : R → R) 1 := fun event => by simp

/-- A bijective decoding is exact: every event of the decoded value has its
uniform probability. -/
theorem prEvent_of_bijective [Fintype B] [Fintype R] {decode : B → R}
    (bijective : Function.Bijective decode) (event : R → Prop) :
    Pr{let answer ← $ᵗ B}[event (decode answer)] = Pr{let value ← $ᵗ R}[event value] := by
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    Fintype.card_of_bijective bijective]
  have counted : (Finset.univ.filter fun answer => event (decode answer)).card =
      (Finset.univ.filter event).card :=
    Finset.card_bij (fun answer _ => decode answer)
      (fun answer member => by simpa using member)
      (fun _ _ _ _ same => bijective.1 same)
      (fun value member => by
        obtain ⟨answer, rfl⟩ := bijective.2 value
        exact ⟨answer, by simpa using member, rfl⟩)
  rw [counted]

/-- A bijective decoding is exact: the decoded value is uniform. -/
theorem dominated_of_bijective [Fintype B] [Fintype R] {decode : B → R}
    (bijective : Function.Bijective decode) : Dominated decode 1 :=
  fun event => by rw [one_mul, prEvent_of_bijective bijective]

/-- Point bounds bound every event by the number of its values. -/
theorem PointBound.dominated [Fintype R] {decode : B → R} {bound : ENNReal}
    (bounded : PointBound decode bound) : Dominated decode (bound * Fintype.card R) := by
  classical
  intro event
  have cover : Pr{let answer ← $ᵗ B}[event (decode answer)] ≤
      ∑ value ∈ Finset.univ.filter event, Pr{let answer ← $ᵗ B}[decode answer = value] :=
    (prEvent_mono _ _ (fun answer => ∃ value ∈ Finset.univ.filter event, decode answer = value)
      fun answer holds => ⟨decode answer, by simpa using holds, rfl⟩).trans
      (prEvent_exists_finset_le _ _ fun value answer => decode answer = value)
  have nonzero : (Fintype.card R : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := R)).ne'
  calc Pr{let answer ← $ᵗ B}[event (decode answer)]
      ≤ ∑ value ∈ Finset.univ.filter event, Pr{let answer ← $ᵗ B}[decode answer = value] := cover
    _ ≤ ∑ _value ∈ Finset.univ.filter event, bound := Finset.sum_le_sum fun value _ => bounded value
    _ = (Finset.univ.filter event).card * bound := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = bound * Fintype.card R * ((Finset.univ.filter event).card / Fintype.card R) := by
        rw [mul_assoc, ENNReal.mul_div_cancel' (fun zero => absurd zero nonzero)
          (fun top => absurd top (ENNReal.natCast_ne_top _)), mul_comm]
    _ = bound * Fintype.card R * Pr{let value ← $ᵗ R}[event value] := by
        rw [SampleableType.prEvent_uniformSample]

omit [SampleableType R] in
/-- A decoding whose every fiber has at most `fiber` answers has point bound
`fiber / |B|`. -/
theorem pointBound_of_fibers [Fintype B] [DecidableEq R] (decode : B → R) (fiber : ℕ)
    (small : ∀ value, (Finset.univ.filter fun answer => decode answer = value).card ≤ fiber) :
    PointBound decode (fiber / Fintype.card B) := by
  intro value
  rw [SampleableType.prEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast small value) _

omit [SampleableType R] in
/-- A refusing decoding whose fiber at `value` has at most `fiber` answers
yields `value` with probability at most `fiber / |B|`. -/
theorem pointBound_of_fibers' [Fintype B] [DecidableEq R] (decode : B → Option R) (value : R)
    (fiber : ℕ)
    (small : (Finset.univ.filter fun answer => decode answer = some value).card ≤ fiber) :
    Pr{let answer ← $ᵗ B}[decode answer = some value] ≤ fiber / Fintype.card B := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast small) _

/-- The realized law of a decoding that may refuse, against the uniform law of
the sort: every event of the successfully decoded value has probability at most
`factor` times its uniform probability plus `slack`. The inequality is about the
joint decoded value, so a block decoded from one answer needs a joint law, not
one per entry. Refused answers stop the verifier and belong to no event; their
probability is a separate, completeness-side quantity. -/
def Realized (decode : B → Option R) (factor slack : ENNReal) : Prop :=
  ∀ event : R → Prop,
    Pr{let answer ← $ᵗ B}[∃ value, decode answer = some value ∧ event value] ≤
      factor * Pr{let value ← $ᵗ R}[event value] + slack

/-- A site whose escape set has uniform probability at most `error` escapes
under a realized decoding with probability at most `factor * error + slack`. -/
theorem Realized.escape_le {decode : B → Option R} {factor slack : ENNReal}
    (realized : Realized decode factor slack) (event : R → Prop) {error : ENNReal}
    (bounded : Pr{let value ← $ᵗ R}[event value] ≤ error) :
    Pr{let answer ← $ᵗ B}[∃ value, decode answer = some value ∧ event value] ≤
      factor * error + slack :=
  (realized event).trans (by gcongr)

theorem Realized.mono {decode : B → Option R} {factor slack factor' slack' : ENNReal}
    (realized : Realized decode factor slack) (factorLe : factor ≤ factor')
    (slackLe : slack ≤ slack') : Realized decode factor' slack' :=
  fun event => (realized event).trans (by gcongr)

/-- A total decoding dominated by `factor` is realized with that factor and no
slack. -/
theorem Dominated.realized {decode : B → R} {factor : ENNReal}
    (dominated : Dominated decode factor) :
    Realized (fun answer => some (decode answer)) factor 0 := by
  intro event
  rw [add_zero, prEvent_congr _ _ (fun answer => event (decode answer)) fun answer =>
    ⟨fun ⟨_, decoded, holds⟩ => by
        cases Option.some.inj decoded
        exact holds,
      fun holds => ⟨_, rfl, holds⟩⟩]
  exact dominated event

/-- A bijective decoding is realized exactly: factor one, no slack. -/
theorem realized_of_bijective [Fintype B] [Fintype R] {decode : B → R}
    (bijective : Function.Bijective decode) :
    Realized (fun answer => some (decode answer)) 1 0 :=
  (dominated_of_bijective bijective).realized

/-- Point bounds on the successful values give a realized law. -/
theorem realized_of_pointBound [Fintype R] {decode : B → Option R} {bound : ENNReal}
    (bounded : ∀ value, Pr{let answer ← $ᵗ B}[decode answer = some value] ≤ bound) :
    Realized decode (bound * Fintype.card R) 0 := by
  classical
  intro event
  have cover : Pr{let answer ← $ᵗ B}[∃ value, decode answer = some value ∧ event value] ≤
      ∑ value ∈ Finset.univ.filter event, Pr{let answer ← $ᵗ B}[decode answer = some value] :=
    (prEvent_mono _ _
      (fun answer => ∃ value ∈ Finset.univ.filter event, decode answer = some value)
      fun answer ⟨value, decoded, holds⟩ => ⟨value, by simpa using holds, decoded⟩).trans
      (prEvent_exists_finset_le _ _ fun value answer => decode answer = some value)
  have nonzero : (Fintype.card R : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := R)).ne'
  calc Pr{let answer ← $ᵗ B}[∃ value, decode answer = some value ∧ event value]
      ≤ ∑ value ∈ Finset.univ.filter event, Pr{let answer ← $ᵗ B}[decode answer = some value] :=
        cover
    _ ≤ ∑ _value ∈ Finset.univ.filter event, bound := Finset.sum_le_sum fun value _ => bounded value
    _ = (Finset.univ.filter event).card * bound := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = bound * Fintype.card R * ((Finset.univ.filter event).card / Fintype.card R) := by
        rw [mul_assoc, ENNReal.mul_div_cancel' (fun zero => absurd zero nonzero)
          (fun top => absurd top (ENNReal.natCast_ne_top _)), mul_comm]
    _ = bound * Fintype.card R * Pr{let value ← $ᵗ R}[event value] + 0 := by
        rw [SampleableType.prEvent_uniformSample, add_zero]

end Laws

section Residues

/-- At most `⌈N / n⌉` elements with distinct indices below `N` share a residue
modulo `n`. -/
theorem residue_card_le {B : Type} [Fintype B] (index : B → ℕ)
    (injective : Function.Injective index) {N : ℕ} (below : ∀ element, index element < N)
    {n : ℕ} (positive : 0 < n) (residue : ℕ) :
    (Finset.univ.filter fun element => index element % n = residue).card ≤ (N + n - 1) / n := by
  classical
  have injOn : Set.InjOn (fun element => index element / n)
      (Finset.univ.filter fun element => index element % n = residue) := by
    intro first firstMember second secondMember same
    rw [Finset.coe_filter] at firstMember secondMember
    have firstResidue : index first % n = residue := by simpa using firstMember
    have secondResidue : index second % n = residue := by simpa using secondMember
    apply injective
    rw [← Nat.div_add_mod (index first) n, ← Nat.div_add_mod (index second) n, firstResidue,
      secondResidue]
    simp only at same
    rw [same]
  calc (Finset.univ.filter fun element => index element % n = residue).card
      ≤ (Finset.range ((N + n - 1) / n)).card := by
        apply Finset.card_le_card_of_injOn _ _ injOn
        intro element _
        simp only [Finset.coe_range, Set.mem_Iio]
        have bounded := below element
        calc index element / n < index element / n + 1 := Nat.lt_succ_self _
          _ = (index element + n) / n := (Nat.add_div_right _ positive).symm
          _ ≤ (N + n - 1) / n := Nat.div_le_div_right (by omega)
    _ = (N + n - 1) / n := Finset.card_range _

/-- The residue modulo `n` of a sample below `N`. -/
def modulo (n : ℕ) [NeZero n] {N : ℕ} (sample : Fin N) : Fin n :=
  ⟨sample.val % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem modulo_fiber (n : ℕ) [NeZero n] (N : ℕ) (value : Fin n) :
    (Finset.univ.filter fun sample : Fin N => modulo n sample = value).card ≤
      (N + n - 1) / n := by
  have same : (Finset.univ.filter fun sample : Fin N => modulo n sample = value) =
      Finset.univ.filter fun sample : Fin N => sample.val % n = value.val := by
    ext sample
    simp [modulo, Fin.ext_iff]
  rw [same]
  exact residue_card_le Fin.val Fin.val_injective Fin.isLt (NeZero.pos n) value.val

/-- Reducing a uniform sample below `N` modulo `n` has point bound `⌈N / n⌉ / N`. -/
theorem modulo_pointBound (n : ℕ) [NeZero n] (N : ℕ) [NeZero N] :
    PointBound (modulo n (N := N)) ((((N + n - 1) / n : ℕ) : ENNReal) / N) := by
  simpa only [Fintype.card_fin] using
    pointBound_of_fibers (modulo n (N := N)) _ (modulo_fiber n N)

/-- Reducing a uniform sample modulo a divisor of its range is exact. -/
theorem modulo_exact (n : ℕ) [NeZero n] (N : ℕ) [NeZero N] (divides : n ∣ N) :
    Dominated (modulo n (N := N)) 1 := by
  obtain ⟨quotient, rfl⟩ := divides
  have dominated := (modulo_pointBound n (n * quotient)).dominated
  refine dominated.mono (le_of_eq ?_)
  have ceiling : (n * quotient + n - 1) / n = quotient := by
    have positive := NeZero.pos n
    rw [show n * quotient + n - 1 = (n - 1) + quotient * n by
      rw [Nat.mul_comm]; omega, Nat.add_mul_div_right _ _ positive,
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have nonzero : (n : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.pos n).ne'
  have quotientNonzero : (quotient : ENNReal) ≠ 0 := by
    have : quotient ≠ 0 := fun zero => NeZero.ne (n * quotient) (by rw [zero, Nat.mul_zero])
    exact_mod_cast this
  have productNonzero : ((quotient : ENNReal) * n) ≠ 0 := mul_ne_zero quotientNonzero nonzero
  have productFinite : ((quotient : ENNReal) * n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  rw [ceiling, Fintype.card_fin, Nat.cast_mul, mul_comm (n : ENNReal), div_eq_mul_inv,
    mul_assoc, mul_comm _ (n : ENNReal), ← mul_assoc, ← div_eq_mul_inv,
    ENNReal.div_self productNonzero productFinite]

/-- The low `bits` bits of the canonical representative of a residue modulo
`p`: the index or proof-of-work test a transcript derives from a squeezed
prime-field element by masking. -/
def lowBits (p bits : ℕ) [NeZero p] (element : ZMod p) : Fin (2 ^ bits) :=
  ⟨element.val % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

theorem lowBits_fiber (p bits : ℕ) [NeZero p] (value : Fin (2 ^ bits)) :
    (Finset.univ.filter fun element : ZMod p => lowBits p bits element = value).card ≤
      (p + 2 ^ bits - 1) / 2 ^ bits := by
  have same : (Finset.univ.filter fun element : ZMod p => lowBits p bits element = value) =
      Finset.univ.filter fun element : ZMod p => element.val % 2 ^ bits = value.val := by
    ext element
    simp [lowBits, Fin.ext_iff]
  rw [same]
  exact residue_card_le ZMod.val (ZMod.val_injective p) ZMod.val_lt (Nat.two_pow_pos bits)
    value.val

/-- Masking a uniform residue modulo `p` to `bits` bits has point bound
`⌈p / 2 ^ bits⌉ / p`. -/
theorem lowBits_pointBound (p bits : ℕ) [NeZero p] :
    PointBound (lowBits p bits) ((((p + 2 ^ bits - 1) / 2 ^ bits : ℕ) : ENNReal) / p) := by
  simpa only [ZMod.card] using pointBound_of_fibers (lowBits p bits) _ (lowBits_fiber p bits)

/-- Masking with refusal: the low `bits` bits of a residue below the largest
multiple of `2 ^ bits` not above `p`, and a refusal above it. A sampler that
reports, instead of resampling, a value outside the range where masking is
uniform has this law. -/
def lowBitsRejecting (p bits : ℕ) [NeZero p] (element : ZMod p) : Option (Fin (2 ^ bits)) :=
  if element.val < 2 ^ bits * (p / 2 ^ bits) then some (lowBits p bits element) else none

theorem lowBitsRejecting_fiber (p bits : ℕ) [NeZero p] (value : Fin (2 ^ bits)) :
    (Finset.univ.filter fun element : ZMod p =>
      lowBitsRejecting p bits element = some value).card ≤ p / 2 ^ bits := by
  classical
  have positive : 0 < 2 ^ bits := Nat.two_pow_pos bits
  have injOn : Set.InjOn (fun element : ZMod p => element.val / 2 ^ bits)
      (Finset.univ.filter fun element : ZMod p =>
        lowBitsRejecting p bits element = some value) := by
    intro first firstMember second secondMember same
    have firstDecoded := (Finset.mem_filter.mp (Finset.mem_coe.mp firstMember)).2
    have secondDecoded := (Finset.mem_filter.mp (Finset.mem_coe.mp secondMember)).2
    have residue : ∀ element : ZMod p, lowBitsRejecting p bits element = some value →
        element.val % 2 ^ bits = value.val := by
      intro element decoded
      unfold lowBitsRejecting at decoded
      split at decoded
      · rw [← Option.some.inj decoded]
        rfl
      · exact absurd decoded (by simp)
    apply ZMod.val_injective p
    simp only at same
    rw [← Nat.div_add_mod first.val (2 ^ bits), ← Nat.div_add_mod second.val (2 ^ bits),
      residue first firstDecoded, residue second secondDecoded, same]
  calc (Finset.univ.filter fun element : ZMod p =>
        lowBitsRejecting p bits element = some value).card
      ≤ (Finset.range (p / 2 ^ bits)).card := by
        apply Finset.card_le_card_of_injOn _ _ injOn
        intro element member
        simp only [Finset.coe_range, Set.mem_Iio]
        have decoded := (Finset.mem_filter.mp (Finset.mem_coe.mp member)).2
        unfold lowBitsRejecting at decoded
        split at decoded
        · rename_i below
          exact (Nat.div_lt_iff_lt_mul positive).mpr (by rw [Nat.mul_comm]; exact below)
        · exact absurd decoded (by simp)
    _ = p / 2 ^ bits := Finset.card_range _

/-- Masking with refusal is dominated by the uniform law of its sort with factor
one and no slack: each successful value has probability at most
`⌊p / 2 ^ bits⌋ / p`, which is at most `2 ^ -bits`. This is a domination, not an
equality; the exact form, the success probability times the uniform law, is
`lowBitsRejecting_exactWithRefusal` (`ZkcSecurity.FiatShamir.Laws`). -/
theorem lowBitsRejecting_realized (p bits : ℕ) [NeZero p] :
    Realized (lowBitsRejecting p bits) 1 0 := by
  have bounded : ∀ value, Pr{let element ← $ᵗ ZMod p}[
      lowBitsRejecting p bits element = some value] ≤ ((p / 2 ^ bits : ℕ) : ENNReal) / p := by
    intro value
    simpa only [ZMod.card] using pointBound_of_fibers' (lowBitsRejecting p bits) value _
      (lowBitsRejecting_fiber p bits value)
  refine (realized_of_pointBound bounded).mono ?_ le_rfl
  have nonzero : (p : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.pos p).ne'
  rw [Fintype.card_fin, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast Nat.div_mul_le_self p (2 ^ bits)

/-- Masking with refusal refuses exactly the residues at or above the largest
multiple of `2 ^ bits` not above `p`: with probability `(p mod 2 ^ bits) / p`,
the completeness cost of a sampler that does not resample. -/
theorem prEvent_lowBitsRejecting_refuses (p bits : ℕ) [NeZero p] :
    Pr{let element ← $ᵗ ZMod p}[lowBitsRejecting p bits element = none] =
      ((p % 2 ^ bits : ℕ) : ENNReal) / p := by
  classical
  rw [SampleableType.prEvent_uniformSample, ZMod.card]
  congr 2
  have counted : (Finset.univ.filter fun element : ZMod p =>
      lowBitsRejecting p bits element = none).card =
        (Finset.Ico (2 ^ bits * (p / 2 ^ bits)) p).card := by
    refine Finset.card_bij (fun element _ => element.val) (fun element member => ?_)
      (fun _ _ _ _ same => ZMod.val_injective p same) (fun index member => ?_)
    · have refused := (Finset.mem_filter.mp member).2
      unfold lowBitsRejecting at refused
      split at refused
      · exact absurd refused (by simp)
      · rename_i above
        exact Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt above, ZMod.val_lt element⟩
    · obtain ⟨lower, upper⟩ := Finset.mem_Ico.mp member
      refine ⟨(index : ZMod p), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · unfold lowBitsRejecting
        simp [ZMod.val_natCast_of_lt upper, Nat.not_lt.mpr lower]
      · exact ZMod.val_natCast_of_lt upper
  rw [counted, Nat.card_Ico, Nat.mod_eq_sub_mul_div]

end Residues

section Products
variable {B₁ B₂ R₁ R₂ : Type} [SampleableType B₁] [SampleableType B₂]

/-- Events of the two coordinates of a uniform pair are independent. -/
theorem prEvent_uniform_prod [Fintype B₁] [Fintype B₂] (first : B₁ → Prop)
    (second : B₂ → Prop) :
    Pr{let answer ← $ᵗ (B₁ × B₂)}[first answer.1 ∧ second answer.2] =
      Pr{let answer ← $ᵗ B₁}[first answer] * Pr{let answer ← $ᵗ B₂}[second answer] := by
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample, Fintype.card_prod]
  have product : (Finset.univ.filter fun answer : B₁ × B₂ => first answer.1 ∧ second answer.2) =
      (Finset.univ.filter first) ×ˢ (Finset.univ.filter second) := by
    ext answer
    simp
  rw [product, Finset.card_product, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_comm (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- Decoding the two coordinates of a uniform pair independently multiplies
their point bounds. -/
theorem PointBound.prod [Fintype B₁] [Fintype B₂] {first : B₁ → R₁} {second : B₂ → R₂}
    {bound₁ bound₂ : ENNReal} (bounded₁ : PointBound first bound₁)
    (bounded₂ : PointBound second bound₂) :
    PointBound (fun answer : B₁ × B₂ => (first answer.1, second answer.2)) (bound₁ * bound₂) := by
  intro value
  rw [prEvent_congr _ _ (fun answer : B₁ × B₂ =>
      first answer.1 = value.1 ∧ second answer.2 = value.2) fun answer => Prod.ext_iff]
  exact (prEvent_uniform_prod (fun component => first component = value.1)
    (fun component => second component = value.2)).trans_le
    (mul_le_mul' (bounded₁ value.1) (bounded₂ value.2))

variable {B R : Type} [SampleableType B]

/-- Events of the coordinates of a uniform tuple are independent. -/
theorem prEvent_uniform_pi [Fintype B] {s : ℕ} (event : Fin s → B → Prop) :
    Pr{let answer ← $ᵗ (Fin s → B)}[∀ index, event index (answer index)] =
      ∏ index, Pr{let answer ← $ᵗ B}[event index answer] := by
  classical
  simp only [SampleableType.prEvent_uniformSample]
  have tuple : (Finset.univ.filter fun answer : Fin s → B => ∀ index, event index (answer index)) =
      Fintype.piFinset fun index => Finset.univ.filter (event index) := by
    ext answer
    simp [Fintype.mem_piFinset]
  rw [tuple, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin, Nat.cast_prod,
    ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.natCast_ne_top _),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]

/-- Decoding every coordinate of a uniform tuple with the same decoder raises
its point bound to the tuple length. -/
theorem PointBound.pi [Fintype B] {decode : B → R} {bound : ENNReal}
    (bounded : PointBound decode bound) (s : ℕ) :
    PointBound (fun answer : Fin s → B => fun index => decode (answer index)) (bound ^ s) := by
  intro value
  rw [prEvent_congr _ _ (fun answer : Fin s → B => ∀ index, decode (answer index) = value index)
      fun answer => funext_iff]
  refine (prEvent_uniform_pi (fun index component => decode component = value index)).trans_le ?_
  calc ∏ index, Pr{let answer ← $ᵗ B}[decode answer = value index]
      ≤ ∏ _index : Fin s, bound := Finset.prod_le_prod fun index _ => bounded (value index)
    _ = bound ^ s := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [SampleableType B] in
/-- A site that reads the first coordinate of a uniform pair keeps its domination
factor. -/
theorem Dominated.comp_fst [SampleableType R] [Fintype B₁] [Fintype B₂] {decode : B₁ → R}
    {factor : ENNReal} (dominated : Dominated decode factor) :
    Dominated (fun answer : B₁ × B₂ => decode answer.1) factor := by
  intro event
  rw [prEvent_congr _ _ (fun answer : B₁ × B₂ => event (decode answer.1) ∧ True)
      fun _ => ⟨fun holds => ⟨holds, trivial⟩, And.left⟩,
    prEvent_uniform_prod (fun component => event (decode component)) (fun _ => True),
    (SampleableType.prEvent_uniformSample_eq_one_iff (fun _ : B₂ => True)).mpr fun _ => trivial,
    mul_one]
  exact dominated event

omit [SampleableType B] in
/-- A site that reads the second coordinate of a uniform pair keeps its
domination factor. -/
theorem Dominated.comp_snd [SampleableType R] [Fintype B₁] [Fintype B₂] {decode : B₂ → R}
    {factor : ENNReal} (dominated : Dominated decode factor) :
    Dominated (fun answer : B₁ × B₂ => decode answer.2) factor := by
  intro event
  rw [prEvent_congr _ _ (fun answer : B₁ × B₂ => True ∧ event (decode answer.2))
      fun _ => ⟨fun holds => ⟨trivial, holds⟩, And.right⟩,
    prEvent_uniform_prod (fun _ => True) (fun component => event (decode component)),
    (SampleableType.prEvent_uniformSample_eq_one_iff (fun _ : B₁ => True)).mpr fun _ => trivial,
    one_mul]
  exact dominated event

/-- A compound draw decoding every coordinate of a uniform tuple has factor
`(bound * |R|) ^ s`, the per-coordinate factor raised to the tuple length. -/
theorem PointBound.dominated_pi [SampleableType R] [Fintype B] [Fintype R] {decode : B → R}
    {bound : ENNReal} (bounded : PointBound decode bound) (s : ℕ) :
    Dominated (fun answer : Fin s → B => fun index => decode (answer index))
      ((bound * Fintype.card R) ^ s) := by
  refine ((bounded.pi s).dominated).mono (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_pow]

end Products

section KoalaBear

/-- The KoalaBear modulus `2 ^ 31 - 2 ^ 24 + 1`. -/
abbrev koalaBear : ℕ := KoalaBear.fieldSize

instance : NeZero koalaBear := ⟨by decide⟩

theorem koalaBear_eq : koalaBear = 2130706433 := by decide

/-- KoalaBear's modulus is one more than a multiple of `2 ^ 24`. -/
theorem koalaBear_sub_one : koalaBear - 1 = 127 * 2 ^ 24 := by decide

/-- Up to 24 bits, a residue class modulo `2 ^ bits` holds at most
`(p - 1) / 2 ^ bits + 1` KoalaBear elements, and this count times `2 ^ bits` is
`p + (2 ^ bits - 1)`. -/
theorem koalaBear_ceiling (bits : ℕ) (small : bits ≤ 24) :
    (koalaBear + 2 ^ bits - 1) / 2 ^ bits * 2 ^ bits = koalaBear + (2 ^ bits - 1) := by
  have split : 2 ^ 24 = 2 ^ bits * 2 ^ (24 - bits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' small]
  have positive : 0 < 2 ^ bits := Nat.two_pow_pos bits
  have multiple : koalaBear + 2 ^ bits - 1 = (127 * 2 ^ (24 - bits) + 1) * 2 ^ bits := by
    have := koalaBear_sub_one
    rw [split] at this
    have atLeast : 1 ≤ koalaBear := NeZero.pos koalaBear
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ (24 - bits)), ← this]
    omega
  rw [multiple, Nat.mul_div_cancel _ positive, ← multiple]
  have atLeast : 1 ≤ 2 ^ bits := positive
  omega

/-- The KoalaBear low-bit factor: `⌈p / 2 ^ bits⌉ / p * 2 ^ bits` is
`1 + (2 ^ bits - 1) / p` up to 24 bits. -/
theorem koalaBear_factor (bits : ℕ) (small : bits ≤ 24) :
    (((koalaBear + 2 ^ bits - 1) / 2 ^ bits : ℕ) : ENNReal) / koalaBear * 2 ^ bits =
      1 + ((2 ^ bits - 1 : ℕ) : ENNReal) / koalaBear := by
  have nonzero : (koalaBear : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.pos koalaBear).ne'
  have counted : (((koalaBear + 2 ^ bits - 1) / 2 ^ bits : ℕ) : ENNReal) * 2 ^ bits =
      ((koalaBear + (2 ^ bits - 1) : ℕ) : ENNReal) := by
    exact_mod_cast koalaBear_ceiling bits small
  rw [div_eq_mul_inv, mul_right_comm, counted, ← div_eq_mul_inv, Nat.cast_add, ENNReal.add_div,
    ENNReal.div_self nonzero (ENNReal.natCast_ne_top _)]

/-- Masking a uniform KoalaBear element to at most 24 bits inflates every event
by at most the factor `1 + (2 ^ bits - 1) / p`. -/
theorem koalaBear_lowBits_dominated (bits : ℕ) (small : bits ≤ 24) :
    Dominated (lowBits koalaBear bits) (1 + ((2 ^ bits - 1 : ℕ) : ENNReal) / koalaBear) := by
  refine (lowBits_pointBound koalaBear bits).dominated.mono (le_of_eq ?_)
  rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, koalaBear_factor bits small]

/-- Every value of a uniform KoalaBear element masked to at most 24 bits has
probability at most `(1 + (2 ^ bits - 1) / p) / 2 ^ bits`. -/
theorem koalaBear_lowBits_pointBound (bits : ℕ) (small : bits ≤ 24) :
    PointBound (lowBits koalaBear bits)
      ((1 + ((2 ^ bits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ bits) := by
  intro value
  refine (lowBits_pointBound koalaBear bits value).trans (le_of_eq ?_)
  have power : (2 : ENNReal) ^ bits ≠ 0 := pow_ne_zero _ two_ne_zero
  have finite : (2 : ENNReal) ^ bits ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [← koalaBear_factor bits small, ENNReal.mul_div_cancel_right power finite]

/-- At 16 bits, the width of a common proof-of-work test, the KoalaBear factor
is `1 + 65535 / 2130706433`. -/
theorem koalaBear_lowBits16_dominated :
    Dominated (lowBits koalaBear 16) (1 + 65535 / 2130706433) := by
  refine (koalaBear_lowBits_dominated 16 (by norm_num)).mono (le_of_eq ?_)
  rw [koalaBear_eq]
  norm_num

/-- At 21 bits, the index width of a `2 ^ 21`-point evaluation domain, the
KoalaBear factor is `1 + 2097151 / 2130706433`. -/
theorem koalaBear_lowBits21_dominated :
    Dominated (lowBits koalaBear 21) (1 + 2097151 / 2130706433) := by
  refine (koalaBear_lowBits_dominated 21 (by norm_num)).mono (le_of_eq ?_)
  rw [koalaBear_eq]
  norm_num

/-- The 16-bit excess lies between `1 / 32513` and `1 / 32512`: about
`2 ^ -14.99`. -/
theorem koalaBear_excess16_bounds :
    (1 : ENNReal) / 32513 < 65535 / 2130706433 ∧ (65535 : ENNReal) / 2130706433 < 1 / 32512 := by
  constructor
  · rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  · rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num

/-- The 21-bit excess is below `1 / 1016`: about `2 ^ -9.99`. -/
theorem koalaBear_excess21_lt : (2097151 : ENNReal) / 2130706433 < 1 / 1016 := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  norm_num

/-- KoalaBear masked to between 1 and 24 bits with refusal refuses only `p - 1`,
with probability `1 / p`. -/
theorem koalaBear_lowBitsRejecting_refuses (bits : ℕ) (positive : 0 < bits)
    (small : bits ≤ 24) :
    Pr{let element ← $ᵗ ZMod koalaBear}[lowBitsRejecting koalaBear bits element = none] =
      1 / koalaBear := by
  rw [prEvent_lowBitsRejecting_refuses]
  congr 2
  have split : 2 ^ 24 = 2 ^ bits * 2 ^ (24 - bits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' small]
  have multiple : koalaBear = 2 ^ bits * (127 * 2 ^ (24 - bits)) + 1 := by
    have := koalaBear_sub_one
    rw [split] at this
    have atLeast : 1 ≤ koalaBear := NeZero.pos koalaBear
    rw [Nat.mul_left_comm, ← this]
    omega
  rw [multiple, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr (by omega)),
    Nat.cast_one]

end KoalaBear

section ScalarReduction

/-- The order `r` of the BLS12-381 scalar field. -/
abbrev bls12381 : ℕ := BLS12_381.scalarFieldSize

instance : NeZero bls12381 := ⟨by decide⟩

/-- A uniform 256-bit integer has at most three preimages of every residue
modulo `r`. -/
theorem bls12381_ceiling : (2 ^ 256 + bls12381 - 1) / bls12381 = 3 := by decide

/-- Reducing a uniform 256-bit integer modulo the BLS12-381 scalar order, as
EIP-4844 derives its evaluation and batching challenges from SHA-256, inflates
every event by at most `3 r / 2 ^ 256`, about `1.3585`. An additive loss for the
same reduction is at least its statistical distance from the uniform residue,
which exceeds any useful round error. -/
theorem bls12381_reduce_dominated :
    Dominated (modulo bls12381 (N := 2 ^ 256)) (3 * bls12381 / 2 ^ 256) := by
  refine (modulo_pointBound bls12381 (2 ^ 256)).dominated.mono (le_of_eq ?_)
  rw [bls12381_ceiling, Fintype.card_fin, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  norm_num

/-- The BLS12-381 reduction factor lies between `1.3585` and `1.3586`. -/
theorem bls12381_factor_bounds :
    (13585 : ENNReal) / 10000 < 3 * bls12381 / 2 ^ 256 ∧
      (3 * bls12381 : ENNReal) / 2 ^ 256 < 13586 / 10000 := by
  have finite : (3 * bls12381 : ENNReal) / 2 ^ 256 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _))
      (by simp)
  have bound : ((13585 : ENNReal) / 10000) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have upper : ((13586 : ENNReal) / 10000) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  constructor
  · rw [← ENNReal.toReal_lt_toReal bound finite]
    simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast, bls12381, BLS12_381.scalarFieldSize]
    norm_num
  · rw [← ENNReal.toReal_lt_toReal finite upper]
    simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast, bls12381, BLS12_381.scalarFieldSize]
    norm_num

end ScalarReduction

end ZkcSecurity.FiatShamir
