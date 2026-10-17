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

end TestsSecurity.SumcheckFiatShamir
