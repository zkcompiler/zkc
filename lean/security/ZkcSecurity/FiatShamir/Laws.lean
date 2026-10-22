module

public import ZkcSecurity.FiatShamir.Obligations
public import ZkcSecurity.FiatShamir.Grinding
public import ZkcSecurity.FiatShamir.Decoding

@[expose] public section

/-! Law records of decoded query sites.

A query site decodes the raw answer of its TranscriptQuery, a uniform value of a
finite type `Raw`, into the sort `Value` the verifier continues with, and may
refuse. Its ideal law is the uniform law of the sort: a uniform field or
extension element for a field challenge, `UniformIndex(N)` for an index below
`N`, and the product law for a block of positions, which is the uniform law of
the function type. A law record (`LawRecord Raw Value`) is the proof-bearing
statement of the realized law that a certificate's error is corrected by:

- `decode : Raw → Option Value`;
- a coefficient `factor` and a slack `slack`, both in `[0, ∞]`, with
  `realized : Realized decode factor slack`: every event of a successfully
  decoded value has probability at most `factor` times its ideal probability
  plus `slack`. A gated accepted-value decoder may have a coefficient below one;
- a refusal bound `refusal` with `refuses_le`, a completeness-side quantity
  that soundness never uses, since a refusal stops the verifier.

A site whose escape set has ideal probability at most `ε` then escapes with
probability at most `factor * ε + slack` (`LawRecord.escape_le`).

Records are presented by five constructors, each from a checked claim about the
realized subdistribution `μ` against the ideal law `ν`:

- `LawRecord.exact`: a total decoding with `μ = ν` (`ExactLaw`), for example a
  bijection (`exactLaw_of_bijective`) or any total decoding dominated with
  factor one (`Dominated.exactLaw`); factor one, no slack, no refusal;
- `LawRecord.exactWithRefusal`: `μ = p_success · ν`
  (`Obligations.ExactWithRefusal`), with the success probability as the
  coefficient. A decoder whose every value has the same number of preimages is
  of this kind (`exactWithRefusal_of_fibers`);
- `LawRecord.dominated`: `μ ≤ κ · ν + λ` with refusal allowed. This suffices
  for soundness but says nothing about the success-conditional law;
- `LawRecord.pointRatio`: `μ(x) ≤ κ · ν(x)` for every value (`PointRatio`);
- `LawRecord.additive`: a total decoding with `κ = 1` and `λ` its additive
  loss (`Balanced`).

`LawRecord.gated` is the accepted-value decoder of a gated site: it refuses
unless the gate passes and otherwise decodes the challenge, with coefficient
and slack a bound on the gate's passing probability times the challenge's (from
`gated_realized`, which uses the independence of the coordinates of a uniform
pair).

The existing sampling lemmas instantiate the records: `identity` and `modulo`
(exact), `lowBitsRejecting` (exact with refusal, from the exact fiber count
`lowBitsRejecting_fiber_eq`), `koalaBearLowBits` (point ratio
`1 + (2 ^ bits - 1) / p`), `bls12381Reduction` (dominated, factor
`3r / 2 ^ 256`), `reduce` (additive, loss `|F| / N`), `koalaBearCompound`
(dominated, factor `(1 + η) ^ s`) and `koalaBearQueryPhase` (gated).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp

section Laws
variable {Raw Value : Type} [SampleableType Raw] [SampleableType Value]

/-- An exact law: every event of the decoded value has its probability under the
uniform law of the sort. -/
def ExactLaw (decode : Raw → Value) : Prop :=
  ∀ event : Value → Prop,
    Pr{let raw ← $ᵗ Raw}[event (decode raw)] = Pr{let value ← $ᵗ Value}[event value]

/-- A bounded point ratio: every value is decoded with probability at most
`factor` times its probability under the uniform law of the sort. -/
def PointRatio (decode : Raw → Option Value) (factor : ENNReal) : Prop :=
  ∀ value, Pr{let raw ← $ᵗ Raw}[decode raw = some value] ≤
    factor * Pr{let other ← $ᵗ Value}[other = value]

/-- A bijective decoding is exact. -/
theorem exactLaw_of_bijective [Fintype Raw] [Fintype Value] {decode : Raw → Value}
    (bijective : Function.Bijective decode) : ExactLaw decode :=
  prEvent_of_bijective bijective

/-- A total decoding dominated with factor one is exact: the complement of every
event is dominated too, and both laws have total mass one. -/
theorem Dominated.exactLaw {decode : Raw → Value} (dominated : Dominated decode 1) :
    ExactLaw decode := by
  intro event
  have below := dominated event
  have complement := dominated fun value => ¬ event value
  rw [one_mul] at below complement
  have decodedTotal := prEvent_add_prEvent_not_eq_prEvent_true ($ᵗ Raw)
    (fun raw => event (decode raw))
  have uniformTotal := prEvent_add_prEvent_not_eq_prEvent_true ($ᵗ Value) event
  rw [prEvent_true_eq_one] at decodedTotal uniformTotal
  have decodedFinite : Pr{let raw ← $ᵗ Raw}[¬ event (decode raw)] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _ _)
  have uniformFinite : Pr{let value ← $ᵗ Value}[¬ event value] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _ _)
  refine le_antisymm below ?_
  calc Pr{let value ← $ᵗ Value}[event value]
      = 1 - Pr{let value ← $ᵗ Value}[¬ event value] :=
        ENNReal.eq_sub_of_add_eq uniformFinite uniformTotal
    _ ≤ 1 - Pr{let raw ← $ᵗ Raw}[¬ event (decode raw)] := tsub_le_tsub_left complement 1
    _ = Pr{let raw ← $ᵗ Raw}[event (decode raw)] :=
        (ENNReal.eq_sub_of_add_eq decodedFinite decodedTotal).symm

/-- An exact total decoding is realized with factor one and no slack. -/
theorem ExactLaw.realized {decode : Raw → Value} (exact : ExactLaw decode) :
    Realized (fun raw => some (decode raw)) 1 0 :=
  Dominated.realized fun event => by rw [exact event, one_mul]

/-- A bounded point ratio gives a realized law with the same coefficient and no
slack. -/
theorem PointRatio.realized [Fintype Value] {decode : Raw → Option Value} {factor : ENNReal}
    (bounded : PointRatio decode factor) : Realized decode factor 0 := by
  classical
  intro event
  have cover : Pr{let raw ← $ᵗ Raw}[∃ value, decode raw = some value ∧ event value] ≤
      ∑ value ∈ Finset.univ.filter event, Pr{let raw ← $ᵗ Raw}[decode raw = some value] :=
    (prEvent_mono _ _
      (fun raw => ∃ value ∈ Finset.univ.filter event, decode raw = some value)
      fun raw ⟨value, decoded, holds⟩ => ⟨value, by simpa using holds, decoded⟩).trans
      (prEvent_exists_finset_le _ _ fun value raw => decode raw = some value)
  calc Pr{let raw ← $ᵗ Raw}[∃ value, decode raw = some value ∧ event value]
      ≤ ∑ value ∈ Finset.univ.filter event, Pr{let raw ← $ᵗ Raw}[decode raw = some value] :=
        cover
    _ ≤ ∑ value ∈ Finset.univ.filter event,
          factor * Pr{let other ← $ᵗ Value}[other = value] :=
        Finset.sum_le_sum fun value _ => bounded value
    _ = factor * Pr{let value ← $ᵗ Value}[event value] := by
        rw [← Finset.mul_sum]
        simp only [SampleableType.prEvent_uniformSample_eq_singleton, Finset.sum_const,
          nsmul_eq_mul, SampleableType.prEvent_uniformSample, div_eq_mul_inv]
    _ = factor * Pr{let value ← $ᵗ Value}[event value] + 0 := (add_zero _).symm

omit [SampleableType Value] in
/-- A refusing decoding whose every value has exactly `fiber` preimages is exact
with refusal: a successful value lands in an event with the success probability
times the event's uniform probability. -/
theorem exactWithRefusal_of_fibers [Fintype Raw] [Fintype Value] [SampleableType Value]
    [DecidableEq Value] (decode : Raw → Option Value) (fiber : ℕ)
    (exactly : ∀ value,
      (Finset.univ.filter fun raw => decode raw = some value).card = fiber) :
    Obligations.ExactWithRefusal decode := by
  classical
  have counted : ∀ event : Value → Prop, [DecidablePred event] →
      (Finset.univ.filter fun raw => ∃ value, decode raw = some value ∧ event value).card =
        (Finset.univ.filter event).card * fiber := by
    intro event _
    have union : (Finset.univ.filter fun raw => ∃ value, decode raw = some value ∧ event value) =
        (Finset.univ.filter event).biUnion fun value =>
          Finset.univ.filter fun raw => decode raw = some value := by
      ext raw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun ⟨value, decoded, holds⟩ => ⟨value, holds, decoded⟩,
        fun ⟨value, holds, decoded⟩ => ⟨value, decoded, holds⟩⟩
    rw [union, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun value _ => exactly value, Finset.sum_const, smul_eq_mul]
    · intro value _ other _ different
      refine Finset.disjoint_left.mpr fun raw first second => different ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at first second
      exact Option.some.inj (first.symm.trans second)
  intro event
  have successes : Pr{let raw ← $ᵗ Raw}[(decode raw).isSome] =
      Pr{let raw ← $ᵗ Raw}[∃ value, decode raw = some value ∧ True] :=
    prEvent_congr _ _ _ fun raw => by
      cases decode raw <;> simp
  rw [successes, SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample, counted, counted, Finset.filter_true]
  have valueNonzero : (Fintype.card Value : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Value)).ne'
  calc (((Finset.univ.filter event).card * fiber : ℕ) : ENNReal) / Fintype.card Raw
      = ((Finset.univ.filter event).card * fiber : ℕ) * (Fintype.card Raw : ENNReal)⁻¹ *
          ((Fintype.card Value : ENNReal) * (Fintype.card Value : ENNReal)⁻¹) := by
        rw [ENNReal.mul_inv_cancel valueNonzero (ENNReal.natCast_ne_top _), mul_one,
          div_eq_mul_inv]
    _ = ((Finset.univ.card * fiber : ℕ) : ENNReal) / Fintype.card Raw *
          ((Finset.univ.filter event).card / Fintype.card Value) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, Finset.card_univ]
        push_cast
        ring

end Laws

/-- A law record of a request class: the decoding of the raw answer into the
sort, a nonnegative coefficient and slack bounding every event of the decoded
value against the uniform law of the sort, and a refusal bound. -/
structure LawRecord (Raw Value : Type) [SampleableType Raw] [SampleableType Value] where
  decode : Raw → Option Value
  factor : ENNReal
  slack : ENNReal
  realized : Realized decode factor slack
  refusal : ENNReal
  refuses_le : Pr{let raw ← $ᵗ Raw}[decode raw = none] ≤ refusal

namespace LawRecord
variable {Raw Value : Type} [SampleableType Raw] [SampleableType Value]

/-- A site whose escape set has ideal probability at most `error` escapes with
probability at most `factor * error + slack`. -/
theorem escape_le (law : LawRecord Raw Value) (event : Value → Prop) {error : ENNReal}
    (bounded : Pr{let value ← $ᵗ Value}[event value] ≤ error) :
    Pr{let raw ← $ᵗ Raw}[∃ value, law.decode raw = some value ∧ event value] ≤
      law.factor * error + law.slack :=
  law.realized.escape_le event bounded

/-- Exact: a total decoding with the uniform law of the sort. -/
def exact (decode : Raw → Value) (exact : ExactLaw decode) : LawRecord Raw Value where
  decode raw := some (decode raw)
  factor := 1
  slack := 0
  realized := exact.realized
  refusal := 0
  refuses_le := le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ => Option.some_ne_none _)

/-- Exact with refusal: the realized subdistribution is the success probability
times the uniform law of the sort, so the success probability is the
coefficient. -/
noncomputable def exactWithRefusal (decode : Raw → Option Value)
    (exact : Obligations.ExactWithRefusal decode) : LawRecord Raw Value where
  decode := decode
  factor := Pr{let raw ← $ᵗ Raw}[(decode raw).isSome]
  slack := 0
  realized event := by rw [exact event, add_zero]
  refusal := Pr{let raw ← $ᵗ Raw}[decode raw = none]
  refuses_le := le_rfl

/-- Dominated with refusal: every event of a successful value is at most
`factor` times its uniform probability plus `slack`. -/
def dominated (decode : Raw → Option Value) (factor slack : ENNReal)
    (realized : Realized decode factor slack) (refusal : ENNReal)
    (refuses_le : Pr{let raw ← $ᵗ Raw}[decode raw = none] ≤ refusal) : LawRecord Raw Value :=
  ⟨decode, factor, slack, realized, refusal, refuses_le⟩

/-- A total dominated decoding, which never refuses. -/
def ofDominated (decode : Raw → Value) (factor : ENNReal) (dominated : Dominated decode factor) :
    LawRecord Raw Value :=
  LawRecord.dominated (fun raw => some (decode raw)) factor 0 dominated.realized 0
    (le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ => Option.some_ne_none _))

/-- Bounded point ratio: every value is at most `factor` times as likely as
under the uniform law of the sort. -/
def pointRatio [Fintype Value] (decode : Raw → Option Value) (factor : ENNReal)
    (bounded : PointRatio decode factor) (refusal : ENNReal)
    (refuses_le : Pr{let raw ← $ᵗ Raw}[decode raw = none] ≤ refusal) : LawRecord Raw Value :=
  ⟨decode, factor, 0, bounded.realized, refusal, refuses_le⟩

/-- Additive: a total decoding whose events exceed their uniform probabilities by
at most `loss`; coefficient one, slack `loss`. -/
def additive (decode : Raw → Value) (loss : ENNReal) (balanced : Balanced decode loss) :
    LawRecord Raw Value where
  decode raw := some (decode raw)
  factor := 1
  slack := loss
  realized := balanced.realized
  refusal := 0
  refuses_le := le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ => Option.some_ne_none _)

/-- The accepted-value decoder of a gated site: the raw answer is a pair of gate
bits and a challenge answer, and the decoder refuses unless the gate passes and
otherwise decodes the challenge. The coefficient and slack are the gate's
passing-probability bound `pass` times the challenge's, and its refusal bound is
the gate's failure-probability bound plus the challenge's. -/
noncomputable def gated {Bits Gate Challenge : Type} [SampleableType Bits] [SampleableType Challenge]
    [Fintype Bits] [Fintype Challenge] [DecidableEq Gate] (gate : Bits → Gate) (passing : Gate)
    {pass : ENNReal} (passes : Pr{let bits ← $ᵗ Bits}[gate bits = passing] ≤ pass)
    {gateFails : ENNReal} (fails : Pr{let bits ← $ᵗ Bits}[gate bits ≠ passing] ≤ gateFails)
    (challenge : LawRecord Challenge Value) : LawRecord (Bits × Challenge) Value where
  decode answer := if gate answer.1 = passing then challenge.decode answer.2 else none
  factor := pass * challenge.factor
  slack := pass * challenge.slack
  realized := gated_realized gate passing challenge.decode passes challenge.realized
  refusal := gateFails + challenge.refusal
  refuses_le := by
    refine (prEvent_mono _ _
      (fun answer : Bits × Challenge => gate answer.1 ≠ passing ∨ challenge.decode answer.2 = none)
      fun answer refused => ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_))
    · by_cases open_ : gate answer.1 = passing
      · simp only [open_, ↓reduceIte] at refused
        exact Or.inr refused
      · exact Or.inl open_
    · have marginal := prEvent_uniform_prod (B₁ := Bits) (B₂ := Challenge)
        (fun bits => gate bits ≠ passing) (fun _ => True)
      rw [prEvent_true_eq_one, mul_one] at marginal
      rw [prEvent_congr _ _ (fun answer : Bits × Challenge => gate answer.1 ≠ passing ∧ True)
        fun _ => ⟨fun holds => ⟨holds, trivial⟩, fun holds => holds.1⟩, marginal]
      exact fails
    · have marginal := prEvent_uniform_prod (B₁ := Bits) (B₂ := Challenge)
        (fun _ => True) (fun answer => challenge.decode answer = none)
      rw [prEvent_true_eq_one, one_mul] at marginal
      rw [prEvent_congr _ _ (fun answer : Bits × Challenge =>
        True ∧ challenge.decode answer.2 = none) fun _ => ⟨fun holds => ⟨trivial, holds⟩, fun holds => holds.2⟩, marginal]
      exact challenge.refuses_le

end LawRecord

section Instances

/-- The undecoded uniform answer. -/
def LawRecord.identity (Value : Type) [SampleableType Value] : LawRecord Value Value :=
  LawRecord.exact id (Dominated.exactLaw dominated_id)

/-- Reducing a uniform sample below `N` modulo a divisor `n` of `N`: exact. -/
def LawRecord.modulo (n : ℕ) [NeZero n] (N : ℕ) [NeZero N] (divides : n ∣ N) :
    LawRecord (Fin N) (Fin n) :=
  LawRecord.exact (ZkcSecurity.FiatShamir.modulo n) (Dominated.exactLaw (modulo_exact n N divides))

/-- Every value of masking with refusal has exactly `⌊p / 2 ^ bits⌋` preimages. -/
theorem lowBitsRejecting_fiber_eq (p bits : ℕ) [NeZero p] (value : Fin (2 ^ bits)) :
    (Finset.univ.filter fun element : ZMod p =>
      lowBitsRejecting p bits element = some value).card = p / 2 ^ bits := by
  classical
  refine le_antisymm (lowBitsRejecting_fiber p bits value) ?_
  have positive : 0 < 2 ^ bits := Nat.two_pow_pos bits
  have below : ∀ index < p / 2 ^ bits, index * 2 ^ bits + value.val < 2 ^ bits * (p / 2 ^ bits) := by
    intro index bounded
    calc index * 2 ^ bits + value.val < index * 2 ^ bits + 2 ^ bits :=
          Nat.add_lt_add_left value.isLt _
      _ = 2 ^ bits * (index + 1) := by ring
      _ ≤ 2 ^ bits * (p / 2 ^ bits) := Nat.mul_le_mul_left _ bounded
  have fits : ∀ index < p / 2 ^ bits, index * 2 ^ bits + value.val < p := fun index bounded =>
    (below index bounded).trans_le (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self p _)
  calc p / 2 ^ bits = (Finset.range (p / 2 ^ bits)).card := (Finset.card_range _).symm
    _ ≤ _ := by
        refine Finset.card_le_card_of_injOn
          (fun index => ((index * 2 ^ bits + value.val : ℕ) : ZMod p)) ?_ ?_
        · intro index member
          have bounded := Finset.mem_range.mp (Finset.mem_coe.mp member)
          simp only [Finset.coe_filter, Finset.mem_univ, true_and]
          change ZkcSecurity.FiatShamir.lowBitsRejecting p bits _ = some value
          unfold ZkcSecurity.FiatShamir.lowBitsRejecting
          simp only [ZMod.val_natCast_of_lt (fits index bounded), below index bounded, ↓reduceIte]
          congr 1
          apply Fin.ext
          simp only [lowBits, ZMod.val_natCast_of_lt (fits index bounded)]
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt value.isLt]
        · intro index member other otherMember same
          have bounded := Finset.mem_range.mp (Finset.mem_coe.mp member)
          have otherBounded := Finset.mem_range.mp (Finset.mem_coe.mp otherMember)
          have vals := congrArg ZMod.val same
          simp only [ZMod.val_natCast_of_lt (fits index bounded),
            ZMod.val_natCast_of_lt (fits other otherBounded)] at vals
          have := Nat.add_right_cancel vals
          exact Nat.eq_of_mul_eq_mul_right positive this

/-- Masking with refusal is exact with refusal: each successful value has
probability `⌊p / 2 ^ bits⌋ / p`, the success probability times `2 ^ -bits`. -/
theorem lowBitsRejecting_exactWithRefusal (p bits : ℕ) [NeZero p] :
    Obligations.ExactWithRefusal (lowBitsRejecting p bits) :=
  exactWithRefusal_of_fibers _ _ (lowBitsRejecting_fiber_eq p bits)

/-- Masking a uniform residue modulo `p` to `bits` bits with refusal: exact with
refusal. -/
noncomputable def LawRecord.lowBitsRejecting (p bits : ℕ) [NeZero p] : LawRecord (ZMod p) (Fin (2 ^ bits)) :=
  LawRecord.exactWithRefusal (ZkcSecurity.FiatShamir.lowBitsRejecting p bits)
    (lowBitsRejecting_exactWithRefusal p bits)

/-- Masking a uniform KoalaBear element to at most 24 bits has point ratio
`1 + (2 ^ bits - 1) / p`. -/
theorem koalaBear_lowBits_pointRatio (bits : ℕ) (small : bits ≤ 24) :
    PointRatio (fun element : ZMod koalaBear => some (lowBits koalaBear bits element))
      (1 + ((2 ^ bits - 1 : ℕ) : ENNReal) / koalaBear) := by
  intro value
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, ← div_eq_mul_inv,
    Nat.cast_pow, Nat.cast_ofNat]
  simpa only [Option.some.injEq] using koalaBear_lowBits_pointBound bits small value

/-- Masking a uniform KoalaBear element to at most 24 bits: point ratio. -/
noncomputable def LawRecord.koalaBearLowBits (bits : ℕ) (small : bits ≤ 24) :
    LawRecord (ZMod koalaBear) (Fin (2 ^ bits)) :=
  LawRecord.pointRatio _ _ (koalaBear_lowBits_pointRatio bits small) 0
    (le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ => Option.some_ne_none _))

/-- Reducing a uniform 256-bit integer modulo the BLS12-381 scalar order:
dominated with factor `3r / 2 ^ 256`. -/
noncomputable def LawRecord.bls12381Reduction : LawRecord (Fin (2 ^ 256)) (Fin bls12381) :=
  LawRecord.ofDominated (ZkcSecurity.FiatShamir.modulo bls12381) _ bls12381_reduce_dominated

/-- Reducing a uniform sample below `N` modulo the field size: additive, loss
`|F| / N`. -/
noncomputable def LawRecord.reduce {F : Type} [Fintype F] [Nonempty F] [DecidableEq F] [SampleableType F]
    (numbering : F ≃ Fin (Fintype.card F)) (N : ℕ) [NeZero N] [SampleableType (Fin N)] :
    LawRecord (Fin N) F :=
  LawRecord.additive (ZkcSecurity.FiatShamir.reduce numbering N) _ (balanced_reduce numbering N)

/-- `s` positions masked from a uniform tuple of KoalaBear elements to at most 24
bits: dominated with the block factor `(1 + (2 ^ bits - 1) / p) ^ s`. -/
noncomputable def LawRecord.koalaBearCompound (bits s : ℕ) (small : bits ≤ 24) :
    LawRecord (Fin s → ZMod koalaBear) (Fin s → Fin (2 ^ bits)) :=
  LawRecord.ofDominated _ _ (koalaBear_compound_dominated bits s small)

/-- A KoalaBear query phase gated by a proof-of-work: the gate's low `gateBits`
bits must be zero, and the positions are masked to `indexBits` bits. The
coefficient is the gate's point bound times the block factor, the factor of
`koalaBear_queryPhase_realized`. -/
noncomputable def LawRecord.koalaBearQueryPhase (gateBits indexBits s : ℕ)
    (gateSmall : gateBits ≤ 24) (indexSmall : indexBits ≤ 24) :
    LawRecord (ZMod koalaBear × (Fin s → ZMod koalaBear)) (Fin s → Fin (2 ^ indexBits)) :=
  LawRecord.gated (lowBits koalaBear gateBits) 0 (koalaBear_lowBits_pointBound gateBits gateSmall 0)
    (prEvent_le_one _ _) (LawRecord.koalaBearCompound indexBits s indexSmall)

/-- The gated query phase record has the factor and slack of
`koalaBear_queryPhase_realized`. -/
theorem LawRecord.koalaBearQueryPhase_factor (gateBits indexBits s : ℕ) (gateSmall : gateBits ≤ 24)
    (indexSmall : indexBits ≤ 24) :
    (LawRecord.koalaBearQueryPhase gateBits indexBits s gateSmall indexSmall).factor =
        (1 + ((2 ^ gateBits - 1 : ℕ) : ENNReal) / koalaBear) / 2 ^ gateBits *
          (1 + ((2 ^ indexBits - 1 : ℕ) : ENNReal) / koalaBear) ^ s ∧
      (LawRecord.koalaBearQueryPhase gateBits indexBits s gateSmall indexSmall).slack = 0 := by
  simp [LawRecord.koalaBearQueryPhase, LawRecord.gated, LawRecord.koalaBearCompound,
    LawRecord.ofDominated, LawRecord.dominated]

end Instances

end ZkcSecurity.FiatShamir
