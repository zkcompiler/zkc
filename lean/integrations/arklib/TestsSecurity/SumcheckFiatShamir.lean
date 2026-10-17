import ZkcSecurity.Examples.SumcheckFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the Fiat–Shamir theorems of the imported Sumcheck verifier.

A one-round instance over `ZMod 5` uses the raw public vector `[2, 1]`, whose
multilinear extension is `2 - r` and whose sum is `3`. All premises of the
theorems hold together (`premises`); the bound evaluates to `1 / 5`. The false
claim `0` is not unreachable: the cheating proof `(0, 0)` passes the boundary
check and is accepted exactly when the challenge is `2`, so the event the bound
controls is nonempty. The false-claim premise is necessary: for the true claim
`3` the honest proof is accepted at every challenge. -/

namespace TestsSecurity.SumcheckFiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Construction ZkcExamples.Structured
open Zkc.Polynomial.Multilinear
open ZkcSecurity.FiatShamir ZkcSecurity.Examples.SumcheckFiatShamir
open scoped ENNReal

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5

noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

/-- The raw public vector and its one-variable table: low value `2`, high `1`. -/
def raw : List Scalar := [2, 1]
def table : Table Scalar 1 := fun bits => if bits 0 then 1 else 2

theorem decoded : ofList? 1 raw = some table := by
  unfold ofList? raw table
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, ↓reduceDIte,
    Option.some.injEq]
  funext bits
  cases first : bits 0 <;> simp [ofVector, index, first]

theorem sum_three : raw.sum = 3 := by decide +kernel

theorem false_claim : (0 : Scalar) ≠ raw.sum := by decide +kernel

/-- A concrete deployment context; the theorems quantify over all of them. -/
def context : Context :=
  ⟨"zkl_sumcheck", ["role00000000", "role00000001"], 0, 1, 3, "random.bls12-381.fr/0",
    "merlin3.bls12-381.fr64be/0", [("challenge", "delivery")]⟩

def initial : History Scalar Scalar := [.binding "statement" [.field "bls12-381.fr" 0]]

def handle : Nat := 7

/-- The proof `(0, 0)` for the false claim `0`. -/
def cheat : Proof Scalar Scalar := [.field "bls12-381.fr" 0, .field "bls12-381.fr" 0]

/-- The honest proof `(2, 1)` for the true claim `3`. -/
def honest : Proof Scalar Scalar := [.field "bls12-381.fr" 2, .field "bls12-381.fr" 1]

/-- The cheating prover queries nothing. -/
def cheater : OracleComp (Spec Scalar Scalar) (Proof Scalar Scalar) := pure cheat

theorem cheater_bound : IsTotalQueryBound cheater 0 := trivial

/-- The plain verifier for the instance, equal to the imported one. -/
abbrev plain (claim : Scalar) : PIR.Proc (Actions Scalar Scalar) (Option Bool) :=
  validator SumcheckSourceVerifier.childContext handle 1 table claim

theorem imported_plain (claim : Scalar) :
    importedValidator (G := Scalar) raw claim 1 handle = plain claim :=
  importedValidator_eq 1 (by decide) raw table decoded claim handle

/-- Accepted exactly at the challenge `2`. -/
theorem cheat_accepted_at_two :
    (transform (m := Id) context (fun _ => 2) (plain 0) initial cheat).1 =
      .returned (some true) := by
  decide +kernel

theorem cheat_rejected_elsewhere :
    ∀ challenge : Scalar, challenge ≠ 2 →
      (transform (m := Id) context (fun _ => challenge) (plain 0) initial cheat).1 =
        .returned (some false) := by
  decide +kernel

/-- Without the false-claim premise the verifier accepts with certainty. -/
theorem honest_accepted_everywhere :
    ∀ challenge : Scalar,
      (transform (m := Id) context (fun _ => challenge) (plain 3) initial honest).1 =
        .returned (some true) := by
  decide +kernel

/-- Every premise of the imported theorem holds together; the bound is `1 / 5`. -/
theorem premises :
    Pr{let result ← (simulateQ randomOracle (experiment context
        (importedValidator raw 0 1 handle) initial cheater)).run' ∅}[
      Accepted (· = some true) result.1] ≤ 1 / 5 := by
  have bound := imported_soundness context 1 raw table decoded 0 false_claim handle initial
    cheater 0 cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
    using bound

/-! ### Adaptively chosen statements -/

/-- A binding of all public inputs: three initial events carrying the raw
vector, the claim and the round count. -/
def binding (statement : PublicStatement Scalar) : History Scalar Scalar :=
  [.binding "values" (statement.raw.map (.field "bls12-381.fr")),
    .binding "claim" [.field "bls12-381.fr" statement.claim],
    .binding "rounds" (List.replicate statement.count (.boolean true))]

/-- This binding determines the statement, so the adaptive premise holds. -/
theorem binding_determined : Determined binding := by
  intro statement other rest otherRest same
  obtain ⟨heads, _⟩ := List.append_inj same (by simp [binding])
  simp only [binding, List.cons.injEq, Event.binding.injEq, true_and, and_true] at heads
  obtain ⟨values, claims, rounds⟩ := heads
  have raws : statement.raw = other.raw :=
    (List.map_injective_iff.mpr fun _ _ same => by cases same; rfl) values
  have counts : statement.count = other.count := by
    simpa using congrArg List.length rounds
  have fieldClaims : statement.claim = other.claim := by
    simpa using claims
  cases statement with
  | mk raw claim count table decoded =>
    cases other with
    | mk raw' claim' count' table' decoded' =>
      simp only at raws counts fieldClaims
      subst raws counts fieldClaims
      cases Option.some.inj (decoded.symm.trans decoded')
      rfl

/-- The false statement the cheating prover chooses. -/
def falseStatement : PublicStatement Scalar := ⟨raw, 0, 1, table, decoded⟩

def adaptiveCheater :
    OracleComp (Spec Scalar Scalar) (PublicStatement Scalar × Proof Scalar Scalar) :=
  pure (falseStatement, cheat)

/-- Every premise of the adaptive theorem holds together; the bound is `2 / 5`. -/
theorem adaptive_premises :
    Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context (id : Scalar → Scalar)
        (fun statement : PublicStatement Scalar =>
          importedValidator statement.raw statement.claim statement.count handle)
        binding adaptiveCheater)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤ 2 / 5 := by
  have bound := adaptive_imported_soundness context handle (id : Scalar → Scalar) 0 balanced_id
    binding binding_determined adaptiveCheater 0 trivial
  simpa only [Nat.cast_zero, zero_add, add_zero, ZMod.card, Nat.cast_ofNat, mul_one_div]
    using bound

/-! ### Reduced wide samples -/

/-- The canonical numbering of `ZMod 5`. -/
def numbering : Scalar ≃ Fin (Fintype.card Scalar) := finCongr (ZMod.card 5).symm

/-- The decoding premise holds for reduction of a uniform sample below `8`, with
loss `5 / 8`. -/
theorem reduced_premise : Balanced (reduce numbering 8) ((5 : ENNReal) / 8) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using balanced_reduce numbering 8

/-- The loss is necessary: reduction modulo `5` of a sample below `8` hits `0`
with probability `2 / 8`, more than the uniform `1 / 5`. -/
theorem reduced_not_exact : ¬ Balanced (reduce numbering 8) 0 := by
  intro exact
  have bound := exact (· = 0)
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample, add_zero]
    at bound
  have hits :
      (Finset.univ.filter fun sample : Fin 8 => reduce numbering 8 sample = 0).card = 2 := by
    decide +kernel
  have uniform : (Finset.univ.filter fun challenge : Scalar => challenge = 0).card = 1 := by
    decide +kernel
  rw [hits, uniform, Fintype.card_fin, ZMod.card] at bound
  have real := (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by simp))
    (ENNReal.div_ne_top (by simp) (by simp))).mpr bound
  rw [ENNReal.toReal_div, ENNReal.toReal_div] at real
  norm_num at real

end TestsSecurity.SumcheckFiatShamir
