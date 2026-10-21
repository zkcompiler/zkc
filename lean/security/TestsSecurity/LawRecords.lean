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
sort, its doomed set (`Doomed`, indexed by the absorbed history) is left with
probability at most `1 / 5` at the challenge and `1 / 4` at the block
(`uniformCertificate`). The challenge is read exactly (`LawRecord.identity`);
the block is read by the accepted-value decoder of the gate (`LawRecord.gated`),
which passes with probability at most `1 / 2`. The lifted charged certificate
charges the challenge `1 / 5` and the block `1 / 2 · 1 / 4` (`chargedCertificate`),
and the typed engine bounds the transform's acceptance against a prover with
`queries` queries by `(queries + 2) / 5` (`lifted_soundness`).

**One occurrence at two rounds.** A loop draws twice at the same occurrence,
with no iteration coordinate, from the same exact decoder: the first draw escapes
with probability `1 / 4` and the second with `1 / 2`. Indexed by the absorbed
history, the doomed set carries both errors, and the charge reads the round from
the history: `1 / 4` before the first draw and `1 / 2` before the second
(`loopCertificate`), so the validator's queries cost `1 / 4 + 1 / 2`
(`loop_soundness`). A certificate whose doomed set and errors ignore the history
must charge the occurrence at least `1 / 2` (`historyFree_error_ge`), `1` for the
two draws. -/

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

/-- Residuals, at the histories where the validator reaches them, that accept with
probability zero unless a draw escapes. -/
inductive Doomed : List Event → PIR.Proc signature Bool → Prop
  | start : Doomed [] validator
  | folded (beta : Fin 5) (nonzero : beta ≠ 0) : Doomed [.fold] (afterFold beta)
  | rejected (history : List Event) : Doomed history (.done false)

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

def uniformCertificate :
    UniformCertificate laws (· = true) fun _ operation => uniformError operation where
  doomed := Doomed
  step history process member := by
    cases member with
    | start =>
        change Pr{let beta ← $ᵗ (Fin 5)}[¬ Doomed [.fold] (afterFold beta)] ≤ 5⁻¹
        calc Pr{let beta ← $ᵗ (Fin 5)}[¬ Doomed [.fold] (afterFold beta)]
            ≤ Pr{let beta ← $ᵗ (Fin 5)}[beta = 0] :=
              prEvent_mono _ _ _ fun beta escaping => by
                by_contra nonzero
                exact escaping (.folded beta nonzero)
          _ = 5⁻¹ := by
              rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin,
                Nat.cast_ofNat]
    | folded beta nonzero =>
        change Pr{let block ← $ᵗ (Fin 2 → Fin 4)}[
          ¬ Doomed [.fold, .positions] (.done (decide (beta = 0 ∨ block 0 = 0)))] ≤ 4⁻¹
        rw [← first_position]
        refine prEvent_mono _ _ _ fun block escaping => ?_
        by_contra notZero
        apply escaping
        have rejected : decide (beta = 0 ∨ block 0 = 0) = false := by simp [nonzero, notZero]
        rw [rejected]
        exact .rejected _
    | rejected => exact Bool.false_ne_true

/-- The occurrence errors of the lifted certificate: the challenge's exact law
keeps `1 / 5`, and the gate halves the block's `1 / 4`. -/
noncomputable def eventError : Event → ℝ≥0∞
  | .fold => 5⁻¹
  | .positions => 2⁻¹ * 4⁻¹

noncomputable def chargedCertificate :
    ChargedCertificate laws.absorb (· = true) fun _ event => eventError event :=
  uniformCertificate.charged laws _ fun history operation event sort law site => by
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
  have total := soundness_charged chargedCertificate validator [] Doomed.start (2 * 5⁻¹)
    (QueryBound.chargedCostBound laws.absorb (fun _ event => eventError_le event) validator 2
      validator_queryBound [])
    prover (queries * 5⁻¹)
    (worstCaseCostBound_of_isTotalQueryBound _ (keyCharge_le fun _ event => eventError_le event)
      prover queries proverBound)
  rwa [← add_mul] at total

/-! ### One occurrence at two rounds with unequal errors -/

inductive LoopOp where
  | draw

abbrev LoopReply : LoopOp → Type
  | .draw => Fin 4

abbrev loopSignature : PIR.Signature := ⟨LoopOp, LoopReply⟩

/-- One occurrence, with no iteration coordinate. -/
inductive LoopEvent where
  | draw
  deriving DecidableEq

abbrev LoopRaw : LoopEvent → Type
  | .draw => Fin 4

instance loopRawSampleable : ∀ event, SampleableType (LoopRaw event)
  | .draw => inferInstanceAs (SampleableType (Fin 4))

/-- Both draws read the raw answer exactly. -/
noncomputable def loopLaws : LawInterface loopSignature LoopEvent Unit LoopRaw
  | .draw => .query .draw inferInstance (LawRecord.identity (Fin 4))

/-- The second draw, after a first draw `first`: accept when `first` is `0` or
the second draw is below `2`. -/
def secondRound (first : Fin 4) : PIR.Proc loopSignature Bool :=
  .call (I := loopSignature) .draw fun second => .done (decide (first = 0 ∨ second.val < 2))

def loop : PIR.Proc loopSignature Bool := .call (I := loopSignature) .draw secondRound

inductive LoopDoomed : List LoopEvent → PIR.Proc loopSignature Bool → Prop
  | start : LoopDoomed [] loop
  | second (first : Fin 4) (nonzero : first ≠ 0) : LoopDoomed [.draw] (secondRound first)
  | rejected (history : List LoopEvent) : LoopDoomed history (.done false)

/-- The round's error, read from the history: `1 / 4` before the first draw and
`1 / 2` afterwards. -/
noncomputable def roundError : List LoopEvent → ℝ≥0∞
  | [] => 4⁻¹
  | _ :: _ => 2 / 4

theorem below_two : Pr{let draw ← $ᵗ (Fin 4)}[draw.val < 2] = 2 / 4 := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  have counted : (Finset.univ.filter fun draw : Fin 4 => draw.val < 2).card = 2 := by decide
  rw [counted]
  norm_num

theorem nonzero_draw : Pr{let draw ← $ᵗ (Fin 4)}[draw ≠ 0] = 3 / 4 := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  have counted : (Finset.univ.filter fun draw : Fin 4 => draw ≠ 0).card = 3 := by decide
  rw [counted]
  norm_num

def loopUniform :
    UniformCertificate loopLaws (· = true) fun history _ => roundError history where
  doomed := LoopDoomed
  step history process member := by
    cases member with
    | start =>
        change Pr{let first ← $ᵗ (Fin 4)}[¬ LoopDoomed [.draw] (secondRound first)] ≤ 4⁻¹
        calc Pr{let first ← $ᵗ (Fin 4)}[¬ LoopDoomed [.draw] (secondRound first)]
            ≤ Pr{let first ← $ᵗ (Fin 4)}[first = 0] :=
              prEvent_mono _ _ _ fun first escaping => by
                by_contra nonzero
                exact escaping (.second first nonzero)
          _ = 4⁻¹ := by
              rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin,
                Nat.cast_ofNat]
    | second first nonzero =>
        change Pr{let draw ← $ᵗ (Fin 4)}[
          ¬ LoopDoomed [.draw, .draw] (.done (decide (first = 0 ∨ draw.val < 2)))] ≤ 2 / 4
        rw [← below_two]
        refine prEvent_mono _ _ _ fun draw escaping => ?_
        by_contra notBelow
        apply escaping
        have rejected : decide (first = 0 ∨ draw.val < 2) = false := by simp [nonzero, notBelow]
        rw [rejected]
        exact .rejected _
    | rejected => exact Bool.false_ne_true

/-- The lifted certificate charges each round its own error. -/
noncomputable def loopCertificate :
    ChargedCertificate loopLaws.absorb (· = true) fun history _ => roundError history :=
  loopUniform.charged loopLaws _ fun history operation event sort law site => by
    cases operation
    cases site
    simp [LawRecord.identity, LawRecord.exact]

theorem loop_costBound :
    ChargedCostBound loopLaws.absorb (fun history _ => roundError history) loop [] (4⁻¹ + 2 / 4) :=
  ⟨2 / 4, le_rfl, fun first => ⟨0, by simp [roundError], fun _ => trivial⟩⟩

/-- The loop's acceptance is bounded by the prover's charge plus `1 / 4 + 1 / 2`,
each round charged its own error at the same occurrence. -/
theorem loop_soundness (prover : OracleComp (OracleSpec.ofFn (ByLast LoopRaw)) (List Unit))
    (proverCost : ℝ≥0∞)
    (proverBound : WorstCaseCostBound prover ⟨keyCharge fun history _ => roundError history⟩
      proverCost) :
    Pr{let result ← (simulateQ randomOracle
        (fixedExperiment loopLaws.absorb loop [] prover)).run' ∅}[
      Accepted (· = true) result.1] ≤ proverCost + (4⁻¹ + 2 / 4) :=
  soundness_charged loopCertificate loop [] LoopDoomed.start _ loop_costBound prover proverCost
    proverBound

/-- A certificate whose doomed set and errors ignore the history must charge the
loop's occurrence at least `1 / 2`: either some first draw other than `0` leads
to a doomed second round, which escapes with probability `1 / 2`, or every such
draw escapes at the first round, with probability `3 / 4`. -/
theorem historyFree_error_ge (error : LoopEvent → ℝ≥0∞)
    (certificate : Certificate loopLaws.absorb (· = true) error)
    (doomedLoop : certificate.doomed loop) : 2 / 4 ≤ error .draw := by
  have notTrue : ¬ certificate.doomed (.done true) := fun doomed =>
    certificate.step _ doomed rfl
  by_cases continues : ∃ first, first ≠ 0 ∧ certificate.doomed (secondRound first)
  · obtain ⟨first, nonzero, doomed⟩ := continues
    have step : Pr{let raw ← $ᵗ (LoopRaw LoopEvent.draw)}[
        ∃ value, (LawRecord.identity (Fin 4)).decode raw = some value ∧
          ¬ certificate.doomed (.done (decide (first = 0 ∨ value.val < 2)))] ≤ error .draw :=
      certificate.step _ doomed
    rw [← below_two]
    refine (prEvent_mono _ _ _ fun draw below => ?_).trans step
    refine ⟨draw, rfl, ?_⟩
    have accepted : decide (first = 0 ∨ draw.val < 2) = true := by simp [below]
    rw [accepted]
    exact notTrue
  · have step : Pr{let raw ← $ᵗ (LoopRaw LoopEvent.draw)}[
        ∃ value, (LawRecord.identity (Fin 4)).decode raw = some value ∧
          ¬ certificate.doomed (secondRound value)] ≤ error .draw :=
      certificate.step _ doomedLoop
    calc (2 : ℝ≥0∞) / 4 ≤ 3 / 4 := ENNReal.div_le_div_right (by norm_num) _
      _ = Pr{let draw ← $ᵗ (Fin 4)}[draw ≠ 0] := nonzero_draw.symm
      _ ≤ error .draw :=
          (prEvent_mono _ _ _ fun draw nonzero =>
            ⟨draw, rfl, fun doomed => continues ⟨draw, nonzero, doomed⟩⟩).trans step

end TestsSecurity.LawRecords
