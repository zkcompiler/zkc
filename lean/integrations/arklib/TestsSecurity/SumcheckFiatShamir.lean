import ZkcSecurity.Examples.SumcheckFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the Fiat–Shamir theorems of the imported Sumcheck verifier.

A one-round instance over `ZMod 5` uses the raw public vector `[2, 1]`, whose
multilinear extension is `2 - r` and whose sum is `3`. All premises of the
theorems hold together (`premises`); the bound evaluates to `1 / 5`. The cheating
proof `(0, 0)` for the false claim `0` passes the boundary check and is accepted
exactly at the challenge `2`, so a prover that sends it without any query is
accepted with probability exactly `1 / 5`: the bound is attained. The
false-claim premise is necessary: for the true claim `3` the honest proof is
accepted at every challenge.

For adaptively chosen statements, a binding of the vector, the claim and the
count determines the statement and the adaptive premises hold together. The
determining premise is necessary: with one initial history for every statement,
a prover that asks the challenge of `(0, 0)` first and then chooses a vector it
fits is accepted on a false claim with probability `4 / 5`, above the `3 / 5`
the adaptive bound would give for its one query. Reducing a sample below `8`
modulo `5` satisfies the decoding premise with loss `5 / 8` and violates it with
loss zero. -/

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

/-! ### The bound is attained -/

/-- The history at which the cheating proof's challenge is asked. -/
def cheatKey : History Scalar Scalar :=
  initial ++
    [.message (context.message (SumcheckVerifierLaws.lowSite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 0) context.validator)
      (.field "bls12-381.fr" 0)] ++
    [.message (context.message (SumcheckVerifierLaws.highSite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 0) context.validator)
      (.field "bls12-381.fr" 0)] ++
    [.challenge
      (context.query (SumcheckVerifierLaws.challengeSite SumcheckSourceVerifier.childContext))]

/-- The verifier's result on the cheating proof at the challenge `answer`. -/
def cheatDecision (answer : Scalar) : PIR.Outcome (Option Bool) × Proof Scalar Scalar :=
  (.returned (some (decide ([answer].length = 1 ∧
    extension 1 table (Zkc.Polynomial.coordinates 1 [answer]) = (1 - answer) * 0 + answer * 0))),
    [])

/-- The transform asks one challenge, at `cheatKey`, and decides. -/
theorem cheat_transform :
    transform context historyQuery (plain 0) initial cheat =
      cheatDecision <$> historyQuery cheatKey := by
  simp only [plain, validator, PIR.repeatN, verifierRound, afterLow, afterHigh, afterChallenge,
    terminal, PIR.Proc.bind, cheat, transform, Payload.value, ↓reduceIte, add_zero,
    List.nil_append]
  rfl

theorem cheatDecision_accepted (answer : Scalar) :
    Accepted (· = some true) (cheatDecision answer).1 ↔ answer = 2 := by
  simp only [cheatDecision, Accepted, Option.some.injEq, decide_eq_true_eq]
  revert answer
  decide +kernel

/-- The query-free cheating prover is accepted with probability exactly `1 / 5`. -/
theorem cheater_acceptance :
    Pr{let result ← (simulateQ randomOracle
        (experiment context (importedValidator raw 0 1 handle) initial cheater)).run' ∅}[
      Accepted (· = some true) result.1] = 1 / 5 := by
  rw [imported_plain, experiment, cheater, pure_bind, cheat_transform, simulateQ_map]
  simp only [historyQuery, simulateQ_spec_query, StateT.run'_eq, StateT.run_map,
    randomOracle.run_eq, QueryCache.empty_apply, map_bind, map_pure, bind_assoc, pure_bind]
  change Pr{let answer ← $ᵗ Scalar}[Accepted (· = some true) (cheatDecision answer).1] = 1 / 5
  rw [prEvent_congr _ _ (fun answer => answer = 2) cheatDecision_accepted,
    SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card, Nat.cast_ofNat, one_div]

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

/-! ### Without a determining binding -/

/-- One initial history for every statement. -/
def unbound : PublicStatement Scalar → History Scalar Scalar := fun _ => initial

theorem unbound_not_determined : ¬ Determined unbound := by
  intro determined
  have := congrArg PublicStatement.claim (determined falseStatement
    ⟨raw, 3, 1, table, decoded⟩ [] [] rfl)
  exact absurd this (by decide)

/-- Values `r` and `r - 1`, whose extension vanishes at `r`. -/
def chosenTable (challenge : Scalar) : Table Scalar 1 :=
  fun bits => if bits 0 then challenge - 1 else challenge

theorem chosen_decoded (challenge : Scalar) :
    ofList? 1 [challenge, challenge - 1] = some (chosenTable challenge) := by
  unfold ofList? chosenTable
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, ↓reduceDIte,
    Option.some.injEq]
  funext bits
  cases first : bits 0 <;> simp [ofVector, index, first]

/-- The statement chosen after seeing the challenge `r`: claim `0` on `[r, r - 1]`. -/
def chosenStatement (challenge : Scalar) : PublicStatement Scalar :=
  ⟨[challenge, challenge - 1], 0, 1, chosenTable challenge, chosen_decoded challenge⟩

/-- Ask the challenge of the proof `(0, 0)` first, then choose a statement it fits. -/
def weakProver :
    OracleComp (Spec Scalar Scalar) (PublicStatement Scalar × Proof Scalar Scalar) := do
  let challenge ← historyQuery cheatKey
  pure (chosenStatement challenge, cheat)

theorem weakProver_bound : IsTotalQueryBound weakProver 1 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩

/-- The verifier's result on `(0, 0)` for the statement chosen at `challenge`,
answered `answer`. -/
def weakDecision (challenge answer : Scalar) : PIR.Outcome (Option Bool) × Proof Scalar Scalar :=
  (.returned (some (decide ([answer].length = 1 ∧
    extension 1 (chosenTable challenge) (Zkc.Polynomial.coordinates 1 [answer]) =
      (1 - answer) * 0 + answer * 0))), [])

theorem weak_transform (challenge : Scalar) :
    transform context (decodedQuery id)
        (plainFamily (G := Scalar) handle (chosenStatement challenge))
        (unbound (chosenStatement challenge)) cheat =
      weakDecision challenge <$> liftM ((Spec Scalar Scalar).query cheatKey) := by
  have admitted : (1 : ℕ) ≤ 2 := by decide
  simp only [plainFamily, admitted, ↓reduceIte, chosenStatement, unbound, validator, PIR.repeatN,
    verifierRound, afterLow, afterHigh, afterChallenge, terminal, PIR.Proc.bind, cheat, transform,
    Payload.value, add_zero, List.nil_append, decodedQuery, id_map]
  rfl

theorem weak_event (challenge : Scalar) :
    ((chosenStatement challenge).claim ≠ (chosenStatement challenge).raw.sum ∧
        Accepted (· = some true) (weakDecision challenge challenge).1) ↔ challenge ≠ 3 := by
  simp only [chosenStatement, weakDecision, Accepted, Option.some.injEq, decide_eq_true_eq]
  revert challenge
  decide +kernel

/-- The one-query prover is accepted on a false claim with probability `4 / 5`. -/
theorem weak_acceptance :
    Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context (id : Scalar → Scalar)
        (plainFamily (G := Scalar) handle) unbound weakProver)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] = 4 / 5 := by
  simp only [adaptiveExperiment, weakProver, historyQuery, bind_assoc, pure_bind, weak_transform,
    Functor.map_map, simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, randomOracle.run_eq, QueryCache.empty_apply,
    QueryCache.cacheQuery_self, map_pure, pure_bind]
  change Pr{let challenge ← $ᵗ Scalar}[(chosenStatement challenge).claim ≠
      (chosenStatement challenge).raw.sum ∧
        Accepted (· = some true) (weakDecision challenge challenge).1] = 4 / 5
  rw [prEvent_congr _ _ (fun challenge => challenge ≠ 3) weak_event,
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun challenge : Scalar => challenge ≠ 3).card = 4 := by
    decide +kernel
  rw [count, ZMod.card]
  rfl

/-- `4 / 5` exceeds `(1 + 2) * (1 / 5)`, the adaptive bound for one query. -/
theorem weak_exceeds_bound : ((1 : ℕ) + (2 : ℕ) : ENNReal) * (1 / 5 + 0) < 4 / 5 := by
  have three : ((1 : ℕ) + (2 : ℕ) : ENNReal) * (1 / 5 + 0) = 3 / 5 := by
    rw [add_zero, mul_one_div]
    norm_num
  rw [three, ← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
    (ENNReal.div_ne_top (by simp) (by simp)), ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num

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
