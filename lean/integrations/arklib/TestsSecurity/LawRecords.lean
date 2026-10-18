import ZkcSecurity.FiatShamir.Lifting

/-! Controls for law records and the lifting of uniform-sort certificates.

**Domination says nothing about the success-conditional law.** The decoder that
returns `0` on one outcome of a fair bit and refuses on the other is dominated by
the uniform bit law with coefficient one (`constantOnSuccess_realized`), yet it
is constant on success, so it is not exact with refusal
(`constantOnSuccess_not_exact`). Masking a residue with refusal is exact with
refusal (`LawRecord.lowBitsRejecting`); its coefficient is its success
probability, at most one (`lowBitsRejecting_factor_le`).

**Lifting.** A validator draws a folding challenge in `Fin 5`, then a block of
two positions in `Fin 4` behind a one-bit proof-of-work gate, and accepts when
the challenge is `0` or the first position is `0`. Under uniform replies of each
sort, its doomed set (`Doomed`) is left with probability at most `1 / 5` at the
challenge and `1 / 4` at the block (`uniformCertificate`). The challenge is read
exactly (`LawRecord.identity`); the block is read by the accepted-value decoder
of the gate (`LawRecord.gated`), which passes with probability `1 / 2`. The
lifted typed certificate charges the challenge `1 / 5` and the block
`1 / 2 · 1 / 4` (`typedCertificate`), and the typed engine bounds the transform's
acceptance against a prover with `queries` queries by `(queries + 2) / 5`
(`lifted_soundness`). -/

namespace TestsSecurity.LawRecords
open OracleComp OracleSpec
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Typed
open scoped ENNReal

/-- `0` on one outcome of a fair bit, a refusal on the other. -/
def constantOnSuccess (bit : Bool) : Option Bool := if bit then some false else none

theorem constantOnSuccess_realized : Realized constantOnSuccess 1 0 := by
  intro event
  rw [one_mul, add_zero]
  by_cases holds : event false
  · calc Pr{let bit ← $ᵗ Bool}[∃ value, constantOnSuccess bit = some value ∧ event value]
        = Pr{let bit ← $ᵗ Bool}[bit = true] :=
          prEvent_congr _ _ _ fun bit => by cases bit <;> simp [constantOnSuccess, holds]
      _ = Pr{let value ← $ᵗ Bool}[value = false] := by
          rw [SampleableType.prEvent_uniformSample_eq_singleton,
            SampleableType.prEvent_uniformSample_eq_singleton]
      _ ≤ Pr{let value ← $ᵗ Bool}[event value] :=
          prEvent_mono _ _ _ fun value same => by subst same; exact holds
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun bit => ?_) zero_le
    cases bit <;> simp [constantOnSuccess, holds]

theorem constantOnSuccess_not_exact : ¬ Obligations.ExactWithRefusal constantOnSuccess := by
  intro exact
  have atFalse := exact (· = false)
  have success : Pr{let bit ← $ᵗ Bool}[∃ value, constantOnSuccess bit = some value ∧ value = false] =
      Pr{let bit ← $ᵗ Bool}[bit = true] :=
    prEvent_congr _ _ _ fun bit => by cases bit <;> simp [constantOnSuccess]
  have succeeds : Pr{let bit ← $ᵗ Bool}[(constantOnSuccess bit).isSome] =
      Pr{let bit ← $ᵗ Bool}[bit = true] :=
    prEvent_congr _ _ _ fun bit => by cases bit <;> simp [constantOnSuccess]
  rw [success, succeeds, SampleableType.prEvent_uniformSample_eq_singleton,
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, Nat.cast_ofNat,
    ← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)] at atFalse
  have doubled := inv_inj.mp atFalse
  norm_num at doubled

theorem lowBitsRejecting_factor_le (p bits : ℕ) [NeZero p] :
    (LawRecord.lowBitsRejecting p bits).factor ≤ 1 :=
  prEvent_le_one _ _

/-! ### A validator with an exact challenge and a gated block -/

/-- The validator's operations: a folding challenge and a gated block. -/
inductive Op where
  | fold
  | positions

/-- Replies: a challenge in `Fin 5` and two positions in `Fin 4`. -/
abbrev Reply : Op → Type
  | .fold => Fin 5
  | .positions => Fin 2 → Fin 4

abbrev signature : PIR.Signature := ⟨Op, Reply⟩

/-- Absorbed events: the two occurrences. -/
inductive Event where
  | fold
  | positions
  deriving DecidableEq

/-- Raw answers by occurrence: the challenge, and gate bits with the block. -/
abbrev Raw : Event → Type
  | .fold => Fin 5
  | .positions => Fin 2 × (Fin 2 → Fin 4)

instance rawSampleable : ∀ event, SampleableType (Raw event)
  | .fold => inferInstanceAs (SampleableType (Fin 5))
  | .positions => inferInstanceAs (SampleableType (Fin 2 × (Fin 2 → Fin 4)))

/-- The gate passes on `0`, with probability `1 / 2`. -/
theorem gate_passes : Pr{let bits ← $ᵗ Fin 2}[id bits = 0] ≤ 2⁻¹ := by
  change Pr{let bits ← $ᵗ Fin 2}[bits = 0] ≤ 2⁻¹
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, Nat.cast_ofNat]

/-- The law interface: the challenge is read exactly, the block through the
gate's accepted-value decoder. -/
noncomputable def laws : LawInterface signature Event Unit Raw
  | .fold => .query .fold inferInstance (LawRecord.identity (Fin 5))
  | .positions => .query .positions inferInstance
      (LawRecord.gated (Bits := Fin 2) id 0 gate_passes (prEvent_le_one _ _)
        (LawRecord.identity (Fin 2 → Fin 4)))

/-- After the challenge `beta`: draw the block and accept when `beta` or the first
position is `0`. -/
def afterFold (beta : Fin 5) : PIR.Proc signature Bool :=
  .call (I := signature) .positions fun block => .done (decide (beta = 0 ∨ block 0 = 0))

def validator : PIR.Proc signature Bool := .call (I := signature) .fold afterFold

/-- Residuals that accept with probability zero unless a draw escapes. -/
inductive Doomed : PIR.Proc signature Bool → Prop
  | start : Doomed validator
  | folded (beta : Fin 5) (nonzero : beta ≠ 0) : Doomed (afterFold beta)
  | rejected : Doomed (.done false)

/-- The uniform-sort errors: `1 / 5` at the challenge, `1 / 4` at the block. -/
noncomputable def uniformError : Op → ℝ≥0∞
  | .fold => 5⁻¹
  | .positions => 4⁻¹

theorem first_position : Pr{let block ← $ᵗ (Fin 2 → Fin 4)}[block 0 = 0] = 4⁻¹ := by
  have product := prEvent_uniform_pi (B := Fin 4) (s := 2)
    fun (index : Fin 2) (position : Fin 4) => index = 0 → position = 0
  rw [Fin.prod_univ_two] at product
  have first : Pr{let position ← $ᵗ Fin 4}[(0 : Fin 2) = 0 → position = 0] = 4⁻¹ := by
    refine (prEvent_congr _ _ (fun position : Fin 4 => position = 0)
      fun _ => ⟨fun zero => zero rfl, fun zero _ => zero⟩).trans ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, Nat.cast_ofNat]
  have second : Pr{let position ← $ᵗ Fin 4}[(1 : Fin 2) = 0 → position = 0] = 1 := by
    refine (prEvent_congr _ _ (fun _ : Fin 4 => True)
      fun _ => ⟨fun _ => trivial, fun _ one => absurd one (by decide)⟩).trans ?_
    exact prEvent_true_eq_one _
  rw [first, second, mul_one] at product
  rw [← product]
  exact prEvent_congr _ _ _ fun block =>
    ⟨fun zero index first => by subst first; exact zero, fun all => all 0 rfl⟩

def uniformCertificate : UniformCertificate laws (· = true) uniformError where
  doomed := Doomed
  step process member := by
    cases member with
    | start =>
        change Pr{let beta ← $ᵗ (Fin 5)}[¬ Doomed (afterFold beta)] ≤ 5⁻¹
        calc Pr{let beta ← $ᵗ (Fin 5)}[¬ Doomed (afterFold beta)]
            ≤ Pr{let beta ← $ᵗ (Fin 5)}[beta = 0] :=
              prEvent_mono _ _ _ fun beta escaping => by
                by_contra nonzero
                exact escaping (.folded beta nonzero)
          _ = 5⁻¹ := by
              rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin,
                Nat.cast_ofNat]
    | folded beta nonzero =>
        change Pr{let block ← $ᵗ (Fin 2 → Fin 4)}[
          ¬ Doomed (.done (decide (beta = 0 ∨ block 0 = 0)))] ≤ 4⁻¹
        rw [← first_position]
        refine prEvent_mono _ _ _ fun block escaping => ?_
        by_contra notZero
        apply escaping
        have rejected : decide (beta = 0 ∨ block 0 = 0) = false := by simp [nonzero, notZero]
        rw [rejected]
        exact .rejected
    | rejected => exact Bool.false_ne_true

/-- The occurrence errors of the lifted certificate: the challenge's exact law
keeps `1 / 5`, and the gate halves the block's `1 / 4`. -/
noncomputable def eventError : Event → ℝ≥0∞
  | .fold => 5⁻¹
  | .positions => 2⁻¹ * 4⁻¹

noncomputable def typedCertificate : Certificate laws.absorb (· = true) eventError :=
  uniformCertificate.certificate laws eventError fun operation event sort law site => by
    cases operation <;> cases site <;>
      simp [LawRecord.identity, LawRecord.exact, LawRecord.gated, uniformError, eventError]

theorem eventError_le (event : Event) : eventError event ≤ 5⁻¹ := by
  cases event
  · exact le_rfl
  · rw [eventError, ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    exact ENNReal.inv_le_inv.mpr (by norm_num)

theorem validator_queryBound : QueryBound laws.absorb validator 2 :=
  ⟨by norm_num, fun beta => ⟨by norm_num, fun _ => trivial⟩⟩

/-- The typed engine's bound for the lifted certificate: every prover with
`queries` queries is accepted with probability at most `(queries + 2) / 5`. -/
theorem lifted_soundness (prover : OracleComp (OracleSpec.ofFn (ByLast Raw)) (List Unit))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (fixedExperiment laws.absorb validator [] prover)).run' ∅}[
      Accepted (· = true) result.1] ≤ (queries + 2) * 5⁻¹ := by
  exact_mod_cast Typed.soundness typedCertificate eventError_le validator Doomed.start 2
    validator_queryBound [] prover queries proverBound

end TestsSecurity.LawRecords
