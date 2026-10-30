module

public import ZkcSecurity.Transformations.FiatShamir.Sampling

@[expose] public section

/-! Grinding-gated and compound query sites.

A gated site squeezes, from one absorbed transcript prefix ending with the
prover's proof-of-work witness, both the proof-of-work test and the challenge it
gates. Its answer decodes to gate bits and a challenge, and the validator
rejects unless the gate passes. This is the proof-of-work model of ethSTARK
(Theorem 6): the site's error is the probability that the gate passes times the
challenge's error (`gated_escape_le`, `gated_step_le`). The witness is part of
the key, so every grinding attempt is one oracle query, charged the site's
error by the soundness theorems: grinding does not amortize. At zero difficulty
the gate has a single value, which passes (`lowBits_zero_difficulty`), so the
gated bound is the ungated one.

A compound site decodes one answer into several values at once, for example
the `s` query positions of a FRI query phase squeezed from one absorbed prefix.
Its error is the joint escape probability of the block under the uniform law,
`(1 - δ) ^ s` for a query phase over a word `δ`-far from the code, times the
block's sampling factor, `(1 + η) ^ s` for positions masked from prime-field
elements (`koalaBear_compound_dominated`). A query phase gated by a
proof-of-work combines both (`koalaBear_queryPhase_escape_le`).

The one-key model assumes the gate bits and the challenge come from one
absorbed prefix, as in a duplex sponge that squeezes both after absorbing the
witness. For an implementation that derives them from different hash calls keyed
by the same witness, role separation (`ZkcSecurity.FiatShamir.Roles`) gives the
same product law at one fixed key only. Turning such a provider into one oracle
on transcript histories is its provider simulation, which these results assume
and do not prove.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp

section Gate
variable {B₁ B₂ G R : Type} [SampleableType B₁] [SampleableType B₂] [Fintype B₁] [Fintype B₂]

/-- A gated site escapes only when its gate passes and its challenge escapes,
so its escape probability is at most the probability that the gate passes times
the challenge's escape probability. -/
theorem gated_escape_le (gate : B₁ → G) (challenge : B₂ → R) (passes : G → Prop)
    (escapes : G × R → Prop) (challengeEscapes : R → Prop)
    (gated : ∀ bits value, escapes (bits, value) → passes bits ∧ challengeEscapes value) :
    Pr{let answer ← $ᵗ (B₁ × B₂)}[escapes (gate answer.1, challenge answer.2)] ≤
      Pr{let bits ← $ᵗ B₁}[passes (gate bits)] *
        Pr{let answer ← $ᵗ B₂}[challengeEscapes (challenge answer)] :=
  (prEvent_mono _ _
    (fun answer : B₁ × B₂ => passes (gate answer.1) ∧ challengeEscapes (challenge answer.2))
    fun _ escaping => gated _ _ escaping).trans
    (le_of_eq (prEvent_uniform_prod (fun bits => passes (gate bits))
      (fun answer => challengeEscapes (challenge answer))))

/-- The local obligation at a gated query of a validator. If every failing gate
value leads to a doomed residual (the validator rejects), the gated query leaves
the doomed set with probability at most the probability of the passing gate
value times the escape probability of the continuation at that value. -/
theorem gated_step_le {Residual : Type} (doomed : Residual → Prop) (next : G × R → Residual)
    (gate : B₁ → G) (challenge : B₂ → R) (pass : G)
    (rejects : ∀ bits value, bits ≠ pass → doomed (next (bits, value))) :
    Pr{let answer ← $ᵗ (B₁ × B₂)}[¬ doomed (next (gate answer.1, challenge answer.2))] ≤
      Pr{let bits ← $ᵗ B₁}[gate bits = pass] *
        Pr{let answer ← $ᵗ B₂}[¬ doomed (next (pass, challenge answer))] :=
  gated_escape_le gate challenge (· = pass) (fun reply => ¬ doomed (next reply))
    (fun value => ¬ doomed (next (pass, value))) fun bits value escaping => by
      by_cases passing : bits = pass
      · subst passing
        exact ⟨rfl, escaping⟩
      · exact absurd (rejects bits value passing) escaping

/-- The joint law of a gated site's passing values. If the gate passes with
probability at most `pass` and the challenge's decoding is realized with
`factor` and `slack`, the decoding that refuses unless the gate passes is
realized with `pass * factor` and `pass * slack`. The product comes from the
independence of the two coordinates of a uniform pair (`prEvent_uniform_prod`),
not from the marginal laws. -/
theorem gated_realized [SampleableType R] [DecidableEq G] (gate : B₁ → G) (passing : G)
    (challenge : B₂ → Option R) {pass factor slack : ENNReal}
    (passes : Pr{let bits ← $ᵗ B₁}[gate bits = passing] ≤ pass)
    (realized : Realized challenge factor slack) :
    Realized (fun answer : B₁ × B₂ => if gate answer.1 = passing then challenge answer.2 else none)
      (pass * factor) (pass * slack) := by
  intro event
  rw [prEvent_congr _ _ (fun answer : B₁ × B₂ => gate answer.1 = passing ∧
      ∃ value, challenge answer.2 = some value ∧ event value) fun answer => by
        by_cases gated : gate answer.1 = passing <;> simp [gated],
    prEvent_uniform_prod (fun bits => gate bits = passing)
      (fun answer => ∃ value, challenge answer = some value ∧ event value)]
  calc Pr{let bits ← $ᵗ B₁}[gate bits = passing] *
        Pr{let answer ← $ᵗ B₂}[∃ value, challenge answer = some value ∧ event value]
      ≤ pass * (factor * Pr{let value ← $ᵗ R}[event value] + slack) :=
        mul_le_mul' passes (realized event)
    _ = pass * factor * Pr{let value ← $ᵗ R}[event value] + pass * slack := by ring

end Gate

/-- At zero difficulty the gate has a single value, so masking passes. -/
theorem lowBits_zero_difficulty (p : ℕ) [NeZero p] (element : ZMod p) :
    lowBits p 0 element = 0 :=
  Fin.ext (by simp [lowBits])

/-- At zero difficulty the gate passes with probability one, so a gated site's
bound is its challenge's bound. -/
theorem prEvent_lowBits_zero_difficulty (p : ℕ) [NeZero p] :
    Pr{let element ← $ᵗ ZMod p}[lowBits p 0 element = 0] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr (lowBits_zero_difficulty p)

/-- Low-bit positions decoded from a uniform tuple of KoalaBear elements, each
masked to at most 24 bits: the factor of the block is `(1 + (2 ^ bits - 1) / p) ^ s`. -/
theorem koalaBear_compound_dominated (bits s : ℕ) (small : bits ≤ 24) :
    Dominated (fun answer : Fin s → ZMod koalaBear =>
        fun index => lowBits koalaBear bits (answer index))
      ((1 + ((2 ^ bits - 1 : ℕ) : ENNReal) / koalaBear) ^ s) := by
  refine ((koalaBear_lowBits_pointBound bits small).dominated_pi s).mono (le_of_eq ?_)
  have power : (2 : ENNReal) ^ bits ≠ 0 := pow_ne_zero _ two_ne_zero
  have finite : (2 : ENNReal) ^ bits ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_mul_cancel power finite]

/-- A KoalaBear query phase gated by a proof-of-work. One absorbed prefix is
answered by a field element for the gate and `s` field elements for the
positions; the gate keeps `gateBits` low bits and must be zero, and each
position keeps `indexBits` low bits. If the block of positions escapes with
probability at most `error` under the uniform law, the phase escapes with
probability at most the gate's point bound times the block factor times
`error`. -/
theorem koalaBear_queryPhase_escape_le (gateBits indexBits s : ℕ) (gateSmall : gateBits ≤ 24)
    (indexSmall : indexBits ≤ 24)
    (escapes : Fin (2 ^ gateBits) × (Fin s → Fin (2 ^ indexBits)) → Prop)
    (blockEscapes : (Fin s → Fin (2 ^ indexBits)) → Prop)
    (gated : ∀ bits positions, escapes (bits, positions) → bits = 0 ∧ blockEscapes positions)
    {error : ENNReal}
    (uniform : Pr{let positions ← $ᵗ (Fin s → Fin (2 ^ indexBits))}[blockEscapes positions] ≤
      error) :
    Pr{let answer ← $ᵗ (ZMod koalaBear × (Fin s → ZMod koalaBear))}[
        escapes (lowBits koalaBear gateBits answer.1,
          fun index => lowBits koalaBear indexBits (answer.2 index))] ≤
      (1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits *
        ((1 + ((2 ^ indexBits - 1 : ℕ) : ENNReal) / koalaBear) ^ s * error) :=
  (gated_escape_le (lowBits koalaBear gateBits)
    (fun answer : Fin s → ZMod koalaBear => fun index => lowBits koalaBear indexBits (answer index))
    (· = 0) escapes blockEscapes gated).trans
    (mul_le_mul' (koalaBear_lowBits_pointBound gateBits gateSmall 0)
      ((koalaBear_compound_dominated indexBits s indexSmall).escape_le blockEscapes uniform))

/-- The KoalaBear query phase as a decoder that refuses unless the gate is
zero: its passing blocks of positions are realized with the gate's point bound
times the block factor, against the uniform law of the block. -/
theorem koalaBear_queryPhase_realized (gateBits indexBits s : ℕ) (gateSmall : gateBits ≤ 24)
    (indexSmall : indexBits ≤ 24) :
    Realized (fun answer : ZMod koalaBear × (Fin s → ZMod koalaBear) =>
        if lowBits koalaBear gateBits answer.1 = 0 then
          some fun index => lowBits koalaBear indexBits (answer.2 index)
        else none)
      ((1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits *
        (1 + ((2 ^ indexBits - 1 : ℕ) : ENNReal) / koalaBear) ^ s)
      ((1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits * 0) :=
  gated_realized (lowBits koalaBear gateBits) 0
    (fun answer : Fin s → ZMod koalaBear =>
      some fun index => lowBits koalaBear indexBits (answer index))
    (koalaBear_lowBits_pointBound gateBits gateSmall 0)
    (koalaBear_compound_dominated indexBits s indexSmall).realized

/-- The query phase at a common benchmark setting: a 16-bit proof-of-work and
100 positions of 21 bits (a `2 ^ 21`-point domain). The gate passes with
probability at most `32513 / 2130706433`, about `2 ^ -15.99996`, and the block
factor is `(1 + 2097151 / 2130706433) ^ 100`. -/
theorem koalaBear_benchmark_queryPhase_escape_le
    (escapes : Fin (2 ^ 16) × (Fin 100 → Fin (2 ^ 21)) → Prop)
    (blockEscapes : (Fin 100 → Fin (2 ^ 21)) → Prop)
    (gated : ∀ bits positions, escapes (bits, positions) → bits = 0 ∧ blockEscapes positions)
    {error : ENNReal}
    (uniform : Pr{let positions ← $ᵗ (Fin 100 → Fin (2 ^ 21))}[blockEscapes positions] ≤ error) :
    Pr{let answer ← $ᵗ (ZMod koalaBear × (Fin 100 → ZMod koalaBear))}[
        escapes (lowBits koalaBear 16 answer.1,
          fun index => lowBits koalaBear 21 (answer.2 index))] ≤
      32513 / 2130706433 * ((1 + 2097151 / 2130706433) ^ 100 * error) := by
  refine (koalaBear_queryPhase_escape_le 16 21 100 (by norm_num) (by norm_num) escapes
    blockEscapes gated uniform).trans (le_of_eq ?_)
  have gate : (1 + ((2 ^ 16 - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ 16 =
      32513 / 2130706433 := by
    rw [← koalaBear_factor 16 (by norm_num), koalaBear_eq,
      ENNReal.mul_div_cancel_right (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
    norm_num
  have positions : ((1 + ((2 ^ 21 - 1 : ℕ) : ENNReal) / koalaBear)) =
      1 + 2097151 / 2130706433 := by
    rw [koalaBear_eq]
    norm_num
  rw [gate, positions]

/-- The block factor of 100 positions of 21 bits is below `1.104`: masking costs
less than `0.143` bits of the query phase's error. -/
theorem koalaBear_benchmark_block_factor_le :
    ((1 : ENNReal) + 2097151 / 2130706433) ^ 100 ≤ 1104 / 1000 := by
  have excess : (2097151 : ENNReal) / 2130706433 ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have finite : ((1 : ENNReal) + 2097151 / 2130706433) ^ 100 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, excess⟩)
  have value : ((1 : ENNReal) + 2097151 / 2130706433).toReal = 1 + 2097151 / 2130706433 := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top excess, ENNReal.toReal_div]
    norm_num
  rw [← ENNReal.toReal_le_toReal finite (ENNReal.div_ne_top (by norm_num) (by norm_num)),
    ENNReal.toReal_pow, value, ENNReal.toReal_div]
  norm_num

end ZkcSecurity.FiatShamir
