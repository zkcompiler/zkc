import ZkcSecurity.FiatShamir.Lifting
import TestsSecurity.Counterexamples.Support
import Mathlib.Data.ZMod.Basic
import ZkcTools.DeclarationAudit

/-! A protocol whose requests have different result sorts, through the transcript
interface, the certificate and the typed theorem.

The validator receives a claimed scalar in `ZMod 5`, then asks three requests:
a field element, an index below a bound (`Op.index bound`, replying in
`Fin (bound + 1)`) and a block of two field elements. It accepts when the
challenge equals the claim, the index is zero, or the block's two elements
agree: the behaviour of a false statement's verifier that any one lucky reply
rescues.

Each request has its own reply sort and raw answer type: the field and block
requests read their raw answers exactly, and the index request reads a raw
answer below `2 * (bound + 1)` reduced modulo `bound + 1`, an exact law because
the modulus divides the range (`laws`). The raw answer type depends on the
request's bound, so the oracle answers by the last event of a key (`ByLast`).

The doomed residuals meet their uniform-sort obligations with errors `1 / 5` at
the field request, `1 / (bound + 1)` at an index request and `1 / 5` at the
block (`uniformCertificate`); the generic lifting through each request's law
record gives the typed certificate (`certificate`). The validator's queries
charge at most `1 / 5 + 1 / 3 + 1 / 5` (`validator_cost`), so a prover whose
queries charge at most `proverCost` is accepted with probability at most
`proverCost + 11 / 15` (`soundness_bound`).

Control: the query-free prover claiming `0` is accepted with probability exactly
`43 / 75`, one minus the product of the three miss probabilities `4 / 5`,
`2 / 3` and `4 / 5` (`cheater_acceptance`), below the theorem's bound `11 / 15`
(`cheater_bound`): every request contributes, and the bound is not vacuous. -/

namespace TestsSecurity.HeterogeneousRequests
open OracleComp OracleSpec
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Typed
open scoped ENNReal

abbrev Scalar := ZMod 5

/-- The validator's operations: receive a claim, then a field request, an index
request below a bound and a block request. -/
inductive Op where
  | claim
  | field
  | index (bound : ℕ)
  | block
  deriving DecidableEq

/-- Each request replies in its own sort. -/
abbrev signature : PIR.Signature where
  Op := Op
  Reply
    | .claim => Scalar
    | .field => Scalar
    | .index bound => Fin (bound + 1)
    | .block => Scalar × Scalar

/-- Absorbed events: the claim message and one occurrence per request. -/
inductive Event where
  | claim (value : Scalar)
  | field
  | index (bound : ℕ)
  | block
  deriving DecidableEq

/-- The raw answer of each occurrence; an index request's raw answer lies below
twice its range. -/
def Raw : Event → Type
  | .claim _ => Unit
  | .field => Scalar
  | .index bound => Fin (2 * (bound + 1))
  | .block => Scalar × Scalar

instance indexRange (bound : ℕ) : NeZero (2 * (bound + 1)) := ⟨by omega⟩

instance rawSampleable : ∀ event, SampleableType (Raw event)
  | .claim _ => inferInstanceAs (SampleableType Unit)
  | .field => inferInstanceAs (SampleableType Scalar)
  | .index bound => inferInstanceAs (SampleableType (Fin (2 * (bound + 1))))
  | .block => inferInstanceAs (SampleableType (Scalar × Scalar))

/-- The oracle answers every key by the raw answer type of its last event. -/
abbrev Answer : List Event → Type := ByLast Raw

def recoverClaim : Event → Option Scalar
  | .claim value => some value
  | _ => none

/-- The law interface: the field and block requests read their raw answers
exactly, an index request reduces its raw answer modulo its range. -/
def laws : LawInterface signature Event Scalar Raw
  | .claim => .receive Event.claim recoverClaim
  | .field => .query .field (inferInstanceAs (SampleableType Scalar)) (LawRecord.identity Scalar)
  | .index bound =>
      .query (.index bound) (inferInstanceAs (SampleableType (Fin (bound + 1))))
        (LawRecord.modulo (bound + 1) (2 * (bound + 1)) (dvd_mul_left (bound + 1) 2))
  | .block =>
      .query .block (inferInstanceAs (SampleableType (Scalar × Scalar)))
        (LawRecord.identity (Scalar × Scalar))

/-- The transcript interface of the law interface. -/
abbrev absorb : Interface signature Event Scalar Raw := laws.absorb

/-- After the claim, the challenge and the index: the block request, then the
verdict. -/
def afterIndex (claimed challenge : Scalar) (position : Fin 3) : PIR.Proc signature Bool :=
  .call Op.block fun pair =>
    .done (decide (challenge = claimed ∨ position = 0 ∨ pair.1 = pair.2))

/-- After the claim and the challenge: the index request below `3`. -/
def afterField (claimed challenge : Scalar) : PIR.Proc signature Bool :=
  .call (Op.index 2) fun position => afterIndex claimed challenge position

/-- After the claim: the field request. -/
def afterClaim (claimed : Scalar) : PIR.Proc signature Bool :=
  .call Op.field fun challenge => afterField claimed challenge

def validator : PIR.Proc signature Bool := .call Op.claim afterClaim

def accepts (accepted : Bool) : Prop := accepted = true

/-- The doomed residuals: before the claim, before the challenge, before the
index after a missed challenge, before the block after a missed challenge and a
nonzero index, and the rejecting verdict. -/
def doomed (process : PIR.Proc signature Bool) : Prop :=
  process = validator ∨ (∃ claimed, process = afterClaim claimed) ∨
    (∃ claimed challenge, challenge ≠ claimed ∧ process = afterField claimed challenge) ∨
    (∃ claimed challenge position, challenge ≠ claimed ∧ position ≠ 0 ∧
      process = afterIndex claimed challenge position) ∨
    process = .done false

/-- The error of each request in its reply sort. -/
noncomputable def error : Op → ENNReal
  | .claim => 0
  | .field => 5⁻¹
  | .index bound => ((bound : ENNReal) + 1)⁻¹
  | .block => 5⁻¹

/-- The error of each absorbed occurrence. -/
noncomputable def eventError : Event → ENNReal
  | .claim _ => 0
  | .field => 5⁻¹
  | .index bound => ((bound : ENNReal) + 1)⁻¹
  | .block => 5⁻¹

theorem field_error (claimed : Scalar) :
    Pr{let challenge ← $ᵗ Scalar}[¬ doomed (afterField claimed challenge)] ≤ 5⁻¹ := by
  refine (prEvent_mono _ _ (fun challenge => challenge = claimed) fun challenge escaping => ?_).trans
    (le_of_eq ?_)
  · by_contra missed
    exact escaping (.inr (.inr (.inl ⟨claimed, challenge, missed, rfl⟩)))
  · rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card, Nat.cast_ofNat]

theorem index_error (claimed challenge : Scalar) (missed : challenge ≠ claimed) :
    Pr{let position ← $ᵗ (Fin (2 + 1))}[¬ doomed (afterIndex claimed challenge position)] ≤
      (((2 : ℕ) : ENNReal) + 1)⁻¹ := by
  refine (prEvent_mono _ _ (fun position => position = 0) fun position escaping => ?_).trans
    (le_of_eq ?_)
  · by_contra nonzero
    exact escaping (.inr (.inr (.inr (.inl ⟨claimed, challenge, position, missed, nonzero, rfl⟩))))
  · rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
    norm_num

theorem block_error (claimed challenge : Scalar) (position : Fin 3) (missed : challenge ≠ claimed)
    (nonzero : position ≠ 0) :
    Pr{let pair ← $ᵗ (Scalar × Scalar)}[¬ doomed (.done (decide
      (challenge = claimed ∨ position = 0 ∨ pair.1 = pair.2)))] ≤ 5⁻¹ := by
  refine (prEvent_mono _ _ (fun pair : Scalar × Scalar => pair.1 = pair.2)
    fun pair escaping => ?_).trans (le_of_eq ?_)
  · by_contra different
    refine escaping (.inr (.inr (.inr (.inr ?_))))
    simp [missed, nonzero, different]
  · rw [SampleableType.prEvent_uniformSample]
    have diagonal : (Finset.univ.filter fun pair : Scalar × Scalar => pair.1 = pair.2).card = 5 := by
      decide
    rw [diagonal, Fintype.card_prod, ZMod.card]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
    norm_num

/-- The doomed residuals meet their uniform-sort obligations. -/
noncomputable def uniformCertificate : UniformEventCertificate laws accepts error where
  doomed := doomed
  step process member := by
    rcases member with rfl | ⟨claimed, rfl⟩ | ⟨claimed, challenge, missed, rfl⟩ |
      ⟨claimed, challenge, position, missed, nonzero, rfl⟩ | rfl
    · exact fun claimed => .inr (.inl ⟨claimed, rfl⟩)
    · exact field_error claimed
    · exact index_error claimed challenge missed
    · exact block_error claimed challenge position missed nonzero
    · show ¬ accepts false
      simp [accepts]

/-- The typed certificate, by the generic lifting through each request's law
record: every law record here is exact, so the occurrence errors are the
request errors. -/
noncomputable def certificate : Certificate absorb accepts eventError :=
  uniformCertificate.typed laws eventError fun operation event sort law site => by
    cases operation <;> simp only [laws] at site <;> cases site
    · simp [LawRecord.identity, LawRecord.exact, error, eventError]
    · simp [LawRecord.modulo, LawRecord.exact, error, eventError]
    · simp [LawRecord.identity, LawRecord.exact, error, eventError]

/-- The validator's queries charge at most `1 / 5 + 1 / 3 + 1 / 5`. -/
theorem validator_cost :
    CostBound absorb eventError validator (5⁻¹ + ((2 : ℕ) + 1 : ENNReal)⁻¹ + 5⁻¹) := by
  intro claimed
  refine ⟨((2 : ℕ) + 1 : ENNReal)⁻¹ + 5⁻¹, by simp [eventError, add_assoc], fun challenge => ?_⟩
  refine ⟨5⁻¹, by simp [eventError], fun position => ?_⟩
  refine ⟨0, by simp [eventError], fun pair => trivial⟩

/-- Every premise of the fixed-statement theorem holds together: a prover whose
queries charge at most `proverCost` is accepted with probability at most
`proverCost + 1 / 5 + 1 / 3 + 1 / 5`. -/
theorem soundness_bound (prover : OracleComp (OracleSpec.ofFn Answer) (List Scalar))
    (proverCost : ENNReal) (bounded : WorstCaseCostBound prover ⟨keyError eventError⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator [] prover)).run' ∅}[
      Accepted accepts result.1] ≤ proverCost + (5⁻¹ + ((2 : ℕ) + 1 : ENNReal)⁻¹ + 5⁻¹) :=
  soundness_weighted certificate validator (Or.inl rfl) _ validator_cost [] prover proverCost
    bounded

/-- The query-free prover claims `0`. -/
def cheater : OracleComp (OracleSpec.ofFn Answer) (List Scalar) := pure [0]

/-- The theorem bounds the query-free prover's acceptance by `11 / 15`. -/
theorem cheater_bound :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator [] cheater)).run'
        ∅}[Accepted accepts result.1] ≤ 11 / 15 := by
  refine (soundness_bound cheater 0 (by simp [cheater])).trans (le_of_eq ?_)
  rw [zero_add, show (((2 : ℕ) : ENNReal) + 1) = 3 by norm_num,
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

/-- The verdict of the claim `0` at a challenge, a raw index answer and a block. -/
def verdict (challenge : Scalar) (raw : Fin 6) (pair : Scalar × Scalar) : Bool :=
  decide (challenge = 0 ∨ modulo 3 raw = 0 ∨ pair.1 = pair.2)

/-- The transform asks three fresh keys, one per request, and decides. -/
theorem cheater_transform :
    transform absorb (ask (R := Answer)) validator [] [0] =
      (do
        let challenge ← answer (R := Answer) [Event.claim 0, Event.field]
        let raw ← answer (R := Answer) [Event.claim 0, Event.field, Event.index 2]
        let pair ← answer (R := Answer) [Event.claim 0, Event.field, Event.index 2, Event.block]
        pure (PIR.Outcome.returned (verdict challenge raw pair), ([] : List Scalar))) := by
  simp only [validator, afterClaim, afterField, afterIndex, Zkc.Transcript.transform, absorb,
    LawInterface.absorb, laws, recoverClaim, List.nil_append, List.cons_append, ask,
    ReadsByOccurrence.read, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    LawRecord.identity, LawRecord.exact, LawRecord.modulo, id]
  rfl

/-- The three keys are fresh and distinct, so the lazily sampled oracle answers
them by independent uniform samples of the requests' raw answer types. -/
theorem cheater_run :
    (simulateQ randomOracle (transform absorb (ask (R := Answer)) validator [] [0])).run' ∅ =
      (do
        let challenge ← $ᵗ Scalar
        let raw ← $ᵗ (Fin 6)
        let pair ← $ᵗ (Scalar × Scalar)
        pure (PIR.Outcome.returned (verdict challenge raw pair), ([] : List Scalar))) := by
  have second : [Event.claim 0, Event.field, Event.index 2] ≠ [Event.claim 0, Event.field] := by
    decide
  have third₁ : [Event.claim 0, Event.field, Event.index 2, Event.block] ≠
      [Event.claim 0, Event.field] := by decide
  have third₂ : [Event.claim 0, Event.field, Event.index 2, Event.block] ≠
      [Event.claim 0, Event.field, Event.index 2] := by decide
  rw [cheater_transform]
  simp only [answer, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, StateT.run'_eq,
    StateT.run_bind, StateT.run_pure, randomOracle.run_eq, QueryCache.empty_apply,
    QueryCache.cacheQuery_of_ne (h := second), QueryCache.cacheQuery_of_ne (h := third₁),
    QueryCache.cacheQuery_of_ne (h := third₂), map_bind, map_pure, bind_assoc, pure_bind]
  rfl

/-- The three independent draws have total mass one. -/
theorem draws_total :
    Pr{let _challenge ← $ᵗ Scalar; let _raw ← $ᵗ (Fin 6); let _pair ← $ᵗ (Scalar × Scalar)}[True] =
      1 := by
  have outer := prEvent_bind_bind_and ($ᵗ Scalar)
    (do let raw ← $ᵗ (Fin 6); let pair ← $ᵗ (Scalar × Scalar); pure (raw, pair))
    (fun _ => True) (fun _ => True)
  have inner := prEvent_bind_bind_and ($ᵗ (Fin 6)) ($ᵗ (Scalar × Scalar))
    (fun _ => True) (fun _ => True)
  simp only [bind_assoc, pure_bind, and_self] at outer inner
  rw [outer, inner, (SampleableType.prEvent_uniformSample_eq_one_iff fun _ : Scalar => True).mpr
      fun _ => trivial,
    (SampleableType.prEvent_uniformSample_eq_one_iff fun _ : Fin 6 => True).mpr fun _ => trivial,
    (SampleableType.prEvent_uniformSample_eq_one_iff fun _ : Scalar × Scalar => True).mpr
      fun _ => trivial, one_mul, one_mul]

/-- The three requests all miss with probability `4 / 5 * (4 / 6 * 20 / 25)`. -/
theorem draws_miss :
    Pr{let challenge ← $ᵗ Scalar; let raw ← $ᵗ (Fin 6); let pair ← $ᵗ (Scalar × Scalar)}[
      ¬ challenge = 0 ∧ ¬ modulo 3 raw = 0 ∧ ¬ pair.1 = pair.2] = 32 / 75 := by
  have outer := prEvent_bind_bind_and ($ᵗ Scalar)
    (do let raw ← $ᵗ (Fin 6); let pair ← $ᵗ (Scalar × Scalar); pure (raw, pair))
    (fun challenge => ¬ challenge = 0) (fun drawn => ¬ modulo 3 drawn.1 = 0 ∧ ¬ drawn.2.1 = drawn.2.2)
  have inner := prEvent_bind_bind_and ($ᵗ (Fin 6)) ($ᵗ (Scalar × Scalar))
    (fun raw => ¬ modulo 3 raw = 0) (fun pair : Scalar × Scalar => ¬ pair.1 = pair.2)
  simp only [bind_assoc, pure_bind] at outer inner
  have challenges : (Finset.univ.filter fun challenge : Scalar => ¬ challenge = 0).card = 4 := by
    decide
  have raws : (Finset.univ.filter fun raw : Fin 6 => ¬ modulo 3 raw = 0).card = 4 := by
    decide
  have pairs : (Finset.univ.filter fun pair : Scalar × Scalar => ¬ pair.1 = pair.2).card = 20 := by
    decide
  rw [outer, inner, SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample, challenges, raws, pairs, Fintype.card_prod, ZMod.card,
    Fintype.card_fin]
  numerals

/-- The query-free prover is accepted with probability exactly `43 / 75`. -/
theorem cheater_acceptance :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator [] cheater)).run'
        ∅}[Accepted accepts result.1] = 43 / 75 := by
  rw [fixedExperiment, cheater, pure_bind, cheater_run]
  simp only [bind_assoc, pure_bind, Accepted, accepts, verdict, decide_eq_true_eq]
  have total := prEvent_add_prEvent_not_eq_prEvent_true
    (do let challenge ← $ᵗ Scalar; let raw ← $ᵗ (Fin 6); let pair ← $ᵗ (Scalar × Scalar)
        pure (challenge, raw, pair))
    fun drawn => drawn.1 = 0 ∨ modulo 3 drawn.2.1 = 0 ∨ drawn.2.2.1 = drawn.2.2.2
  simp only [bind_assoc, pure_bind, not_or] at total
  rw [draws_total, draws_miss] at total
  rw [← ENNReal.add_left_inj (show (32 / 75 : ENNReal) ≠ ⊤ by finiteness), total,
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

end TestsSecurity.HeterogeneousRequests

run_cmd ZkcTools.DeclarationAudit.checkCurrent "HETEROGENEOUS-REQUESTS-AXIOM-PASS"
