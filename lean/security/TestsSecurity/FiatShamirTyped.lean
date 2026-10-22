import ZkcSecurity.FiatShamir.Roles
import Mathlib.Data.ZMod.Basic

/-! Controls for the Fiat–Shamir theorems over typed query sites.

A gated validator receives a nonce, then draws one gated challenge whose raw
answer is a pair of gate bits in `Fin 2` and a challenge in `ZMod 5`. It rejects
unless the gate bits are zero and accepts exactly at the challenge `2`, the
behaviour of a false statement's verifier against a fixed cheating proof. The
certificate's error at the gated occurrence comes from the gate lemma: the gate
passes with probability `1 / 2` and the challenge escapes with probability
`1 / 5`, so the site's error is `1 / 10` (`certificate`). All premises of the
fixed-statement theorem hold together, with bound `(queries + 1) / 10`
(`premises`). The query-free prover sending the nonce `0` is accepted with
probability exactly `1 / 10` (`cheater_acceptance`): the bound is attained.

Joint laws are not implied by marginal ones: copying one uniform bit into both
coordinates of a pair has uniform coordinates, yet the pair is not dominated by
the uniform law with factor one (`copied_not_dominated`); its factor is two
(`copied_dominated`). The checked sampling factors are restated for reference
(`koalaBear_sixteen`, `koalaBear_twentyOne`, `bls12381_factor`).
-/

namespace TestsSecurity.FiatShamirTyped
open OracleComp OracleSpec
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Typed
open scoped ENNReal

abbrev Scalar := ZMod 5

/-- The validator's operations: receive a nonce, then draw a gated challenge. -/
inductive Op where
  | nonce
  | draw
  deriving DecidableEq

/-- A nonce is one of four values; a draw replies with gate bits and a challenge. -/
abbrev signature : PIR.Signature where
  Op := Op
  Reply
    | .nonce => Fin 4
    | .draw => Fin 2 × Scalar

/-- Absorbed events: a nonce message and the gated occurrence. -/
inductive Event where
  | nonce (value : Fin 4)
  | gated
  deriving DecidableEq

/-- Every occurrence is answered by gate bits and a challenge. -/
abbrev Raw : Event → Type := fun _ => Fin 2 × Scalar

/-- The history oracle answers every history by gate bits and a challenge. -/
abbrev Answer : List Event → Type := fun _ => Fin 2 × Scalar

def recoverNonce : Event → Option (Fin 4)
  | .nonce value => some value
  | .gated => none

/-- The receive absorbs the nonce; the draw decodes the raw pair exactly. -/
def absorb : Interface signature Event (Fin 4) Raw
  | .nonce => .receive Event.nonce recoverNonce
  | .draw => .query .gated fun raw => some raw

/-- After the gated draw: reject unless the gate bits are zero, accept exactly at
the challenge `2`. -/
def afterDraw (reply : Fin 2 × Scalar) : PIR.Process signature Bool :=
  if reply.1 = 0 then .done (decide (reply.2 = 2)) else .halt .reject

def gatedDraw : PIR.Process signature Bool := .call Op.draw afterDraw

def validator : PIR.Process signature Bool := .call Op.nonce fun _ => gatedDraw

def accepts (accepted : Bool) : Prop := accepted = true

/-- The doomed residuals: before the nonce, before the draw, a rejecting result
and every stop. -/
def doomed (process : PIR.Process signature Bool) : Prop :=
  process = validator ∨ process = gatedDraw ∨ process = .done false ∨
    ∃ stop, process = .halt stop

theorem afterDraw_doomed (reply : Fin 2 × Scalar) :
    doomed (afterDraw reply) ↔ ¬ (reply.1 = 0 ∧ reply.2 = 2) := by
  unfold afterDraw doomed validator gatedDraw
  by_cases gate : reply.1 = 0 <;> by_cases challenge : reply.2 = 2 <;> simp [gate, challenge]

/-- The gated occurrence's error: gate `1 / 2` times challenge `1 / 5`. -/
theorem gated_error :
    Pr{let raw ← $ᵗ (Raw Event.gated)}[
      ∃ value, (some raw : Option (Fin 2 × Scalar)) = some value ∧ ¬ doomed (afterDraw value)] ≤
      1 / 10 := by
  have reduced : ∀ raw : Fin 2 × Scalar,
      (∃ value, (some raw : Option (Fin 2 × Scalar)) = some value ∧ ¬ doomed (afterDraw value)) ↔
        ¬ doomed (afterDraw (id raw.1, id raw.2)) :=
    fun raw => ⟨fun ⟨_, decoded, outside⟩ => by
        cases Option.some.inj decoded
        exact outside,
      fun outside => ⟨raw, rfl, outside⟩⟩
  change Pr{let raw ← $ᵗ (Fin 2 × Scalar)}[_] ≤ _
  rw [prEvent_congr _ _ _ reduced]
  refine (gated_step_le doomed afterDraw id id 0 fun bits value different => ?_).trans ?_
  · exact (afterDraw_doomed _).mpr fun passing => different passing.1
  · have challenge : Pr{let answer ← $ᵗ Scalar}[¬ doomed (afterDraw (0, id answer))] = 1 / 5 := by
      rw [prEvent_congr _ _ (fun answer => answer = 2) fun answer => by
          rw [afterDraw_doomed]
          simp,
        SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card, Nat.cast_ofNat, one_div]
    simp only [id_eq] at challenge ⊢
    rw [challenge, SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
    rw [show ((2 : ℕ) : ENNReal)⁻¹ * (1 / 5) = 1 / 10 by
      rw [one_div, one_div, ← ENNReal.mul_inv (by simp) (by simp)]
      norm_num]

/-- The certificate: every doomed residual meets its obligation, with error
`1 / 10` at the gated occurrence. -/
def certificate : Certificate absorb accepts (fun _ => 1 / 10) where
  doomed := doomed
  step process member := by
    rcases member with rfl | rfl | rfl | ⟨stop, rfl⟩
    · intro nonce
      exact Or.inr (Or.inl rfl)
    · exact gated_error
    · show ¬ accepts false
      simp [accepts]
    · trivial

theorem validator_bound : QueryBound absorb validator 1 := by
  intro nonce
  refine ⟨Nat.one_pos, fun reply => ?_⟩
  unfold afterDraw
  split <;> trivial

/-- Every premise of the fixed-statement theorem holds together; the bound is
`(queries + 1) / 10`. -/
theorem premises (prover : OracleComp (OracleSpec.ofFn Answer) (List (Fin 4))) (queries : ℕ)
    (bounded : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator [] prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + 1) * (1 / 10) :=
  soundness certificate (fun _ => le_rfl) validator (Or.inl rfl) 1 validator_bound [] prover
    queries bounded |>.trans (le_of_eq (by rw [Nat.cast_one]))

/-- The query-free prover sends the nonce `0`. -/
def cheater : OracleComp (OracleSpec.ofFn Answer) (List (Fin 4)) := pure [0]

/-- The transform asks one key, at the nonce and the gated occurrence, and decides. -/
theorem cheater_transform :
    transform absorb ask validator [] [0] =
      (fun raw : Fin 2 × Scalar =>
        (if raw.1 = 0 then (PIR.Outcome.returned (decide (raw.2 = 2)), ([] : List (Fin 4)))
          else (.stopped .reject, []))) <$>
        (answer (R := Answer) [Event.nonce 0, Event.gated]) := by
  simp only [validator, gatedDraw, Zkc.Transcript.transform, absorb, recoverNonce, List.nil_append,
    ask, ReadsByOccurrence.read, Equiv.refl_apply, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  congr 1
  funext raw
  unfold afterDraw
  split <;> rfl

/-- The query-free prover is accepted with probability exactly `1 / 10`. -/
theorem cheater_acceptance :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator [] cheater)).run'
        ∅}[Accepted accepts result.1] = 1 / 10 := by
  rw [fixedExperiment, cheater, pure_bind, cheater_transform, simulateQ_map]
  simp only [answer, simulateQ_spec_query, StateT.run'_eq, StateT.run_map,
    randomOracle.run_eq, QueryCache.empty_apply, map_bind, map_pure, bind_assoc, pure_bind]
  change Pr{let raw ← $ᵗ (Fin 2 × Scalar)}[Accepted accepts
    (if raw.1 = 0 then (PIR.Outcome.returned (decide (raw.2 = 2)), ([] : List (Fin 4)))
      else (.stopped .reject, [])).1] = 1 / 10
  rw [prEvent_congr _ _ (fun raw => raw = (0, 2)) fun raw => by
      by_cases gate : raw.1 = 0 <;> by_cases challenge : raw.2 = 2 <;>
        simp [Accepted, accepts, gate, challenge, Prod.ext_iff],
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_prod, Fintype.card_fin,
    ZMod.card]
  norm_num

/-! ### Joint laws are not marginal laws -/

/-- Copy one uniform bit into both coordinates of a pair. -/
def copied (bit : Fin 2) : Fin 2 × Fin 2 := (bit, bit)

/-- Each coordinate of the copied pair is exactly uniform. -/
theorem copied_marginal : Dominated (fun bit : Fin 2 => (copied bit).1) 1 := dominated_id

/-- The copied pair is not dominated by the uniform law with factor one: it is
diagonal with probability one, the uniform pair with probability one half. -/
theorem copied_not_dominated : ¬ Dominated copied 1 := by
  intro dominated
  have diagonal := dominated fun pair => pair.1 = pair.2
  rw [one_mul, prEvent_congr _ _ (fun _ => True) fun bit => by simp [copied],
    (SampleableType.prEvent_uniformSample_eq_one_iff (fun _ : Fin 2 => True)).mpr
      fun _ => trivial, SampleableType.prEvent_uniformSample] at diagonal
  have diagonalCount :
      (Finset.univ.filter fun pair : Fin 2 × Fin 2 => pair.1 = pair.2).card = 2 := by
    decide
  rw [diagonalCount, Fintype.card_prod, Fintype.card_fin] at diagonal
  have half : ((2 : ℕ) : ENNReal) / ((2 * 2 : ℕ) : ENNReal) < 1 := by
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    norm_num
  exact absurd diagonal (not_le.mpr half)

/-- Its factor is two: every point of the copied pair has probability at most
one half. -/
theorem copied_dominated : Dominated copied 2 := by
  refine (pointBound_of_fibers copied 1 fun value => ?_).dominated.mono (le_of_eq ?_)
  · revert value
    decide
  · simp only [Fintype.card_fin, Fintype.card_prod, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
    rw [show (2 * 2 : ENNReal) = 2 * 2 from rfl, one_div, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ### Checked sampling factors -/

theorem koalaBear_sixteen :
    Dominated (lowBits koalaBear 16) (1 + 65535 / 2130706433) :=
  koalaBear_lowBits16_dominated

theorem koalaBear_twentyOne :
    Dominated (lowBits koalaBear 21) (1 + 2097151 / 2130706433) :=
  koalaBear_lowBits21_dominated

theorem bls12381_factor :
    Dominated (modulo bls12381 (N := 2 ^ 256)) (3 * bls12381 / 2 ^ 256) ∧
      (13585 : ENNReal) / 10000 < 3 * bls12381 / 2 ^ 256 :=
  ⟨bls12381_reduce_dominated, bls12381_factor_bounds.1⟩

end TestsSecurity.FiatShamirTyped
