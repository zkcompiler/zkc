import ZkcArkLib.Examples.SumcheckFiatShamir
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
the adaptive bound would give for its one query (`unbound_violates_bound`).
Reducing a sample below `8` modulo `5` satisfies the decoding premise with loss
`5 / 8` and violates it with loss zero; with samples below `64` all premises of
the reduced theorem hold and the bound stays below one.

The remaining theorems have their premises met on the same instance: a
distribution over provers (`randomized_premises`), compiled verifiers given by
their construction equation (`compiled_premises`, `compiled_plain_premises`,
`compiled_adaptive_premises`, `participant_premises`,
`adaptive_participant_premises`), a compiled verifier reporting rejection as a
stop (`image_premises`) and the Reduction root over an external table with one
remaining coordinate (`reduction_premises`). A report that accepts every outcome
violates the outcome-image premise and accepts with probability one
(`acceptAll_exceeds`). -/

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

theorem false_claim : (0 : Scalar) ≠ raw.sum := by decide +kernel

/-- A concrete deployment context; the theorems quantify over all of them. -/
def context : Context :=
  ⟨"zkl_sumcheck", ["role00000000", "role00000001"], 0, 1, 3, "random.bls12-381.fr/0",
    some (.draw "bls12-381.fr"), "merlin3.bls12-381.fr64be/0", [("challenge", "delivery")]⟩

def initial : History Scalar Scalar := [.binding "statement" [.field "bls12-381.fr" 0]]

def handle : Nat := 7

/-- The proof `(0, 0)` for the false claim `0`. -/
def cheat : Proof Scalar Scalar := [.field "bls12-381.fr" 0, .field "bls12-381.fr" 0]

/-- The honest proof `(2, 1)` for the true claim `3`. -/
def honest : Proof Scalar Scalar := [.field "bls12-381.fr" 2, .field "bls12-381.fr" 1]

/-- The cheating prover queries nothing. -/
def cheater : OracleComp (FieldOracle Scalar Scalar) (Proof Scalar Scalar) := pure cheat

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
      (context.query (SumcheckVerifierLaws.challengeSite SumcheckSourceVerifier.childContext)
        (.draw "bls12-381.fr"))]

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
    terminal, decision, PIR.Proc.bind, cheat, transform_eq_done, transform_eq_receive,
    transform_eq_query, transform_eq_send, Payload.value, ↓reduceIte, add_zero,
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
    OracleComp (FieldOracle Scalar Scalar) (PublicStatement Scalar × Proof Scalar Scalar) :=
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
    OracleComp (FieldOracle Scalar Scalar) (PublicStatement Scalar × Proof Scalar Scalar) := do
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
      weakDecision challenge <$> liftM ((FieldOracle Scalar Scalar).query cheatKey) := by
  have admitted : (1 : ℕ) ≤ 2 := by decide
  simp only [plainFamily, admitted, ↓reduceIte, chosenStatement, unbound, validator, PIR.repeatN,
    verifierRound, afterLow, afterHigh, afterChallenge, terminal, decision, PIR.Proc.bind, cheat,
    transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
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

/-- The adaptive conclusion fails without a determining initial history: the
one-query prover exceeds `(1 + 2) * (1 / 5 + 0)`. -/
theorem unbound_violates_bound :
    ¬ Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context (id : Scalar → Scalar)
        (plainFamily (G := Scalar) handle) unbound weakProver)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      ((1 : ℕ) + (2 : ℕ) : ENNReal) * (1 / 5 + 0) := fun bound =>
  absurd (weak_acceptance.symm.le.trans bound) (not_le.mpr weak_exceeds_bound)

/-! ### Private randomness and composition -/

/-- The plain verifier's certificate for the instance. -/
noncomputable abbrev instanceCertificate :=
  certificate (G := Scalar) SumcheckSourceVerifier.childContext handle 1 table (decision 1 table)
    (· = some true) (decision_rejects table)

theorem plain_doomed : instanceCertificate.doomed (plain 0) :=
  ⟨.round 1 [] 0, ⟨rfl, falseClaim_initial table 0 (by decide +kernel)⟩, rfl⟩

/-- A fair coin chooses between the cheating proof and the honest proof. -/
noncomputable def drawnProvers :
    ProbComp (OracleComp (FieldOracle Scalar Scalar) (Proof Scalar Scalar)) :=
  (fun coin : Bool => if coin then cheater else pure honest) <$> ($ᵗ Bool)

/-- The premises of `randomized_soundness` hold for a distribution over two
provers, each without queries. -/
theorem randomized_premises :
    Pr{let result ← drawnProvers >>= fun prover =>
        (simulateQ randomOracle (experiment context (plain 0) initial prover)).run' ∅}[
      Accepted (· = some true) result.1] ≤ ((0 : ℕ) + (1 : ℕ)) * (1 / 5) := by
  have bound := randomized_soundness instanceCertificate context (plain 0) plain_doomed 1
    (residual_queryBound SumcheckSourceVerifier.childContext handle (decision 1 table) 1 [] 0)
    initial drawnProvers 0 (by
      intro prover drawn
      rw [drawnProvers, support_map] at drawn
      obtain ⟨coin, _, rfl⟩ := drawn
      cases coin <;> trivial)
  simpa only [ZMod.card, Nat.cast_ofNat] using bound

/-- The compiled verifier given by its construction equation, so the
construction premise holds by definition. -/
def compiledVerifier (proof : Proof Scalar Scalar) :
    OracleComp (FieldOracle Scalar Scalar) (PIR.Outcome (Option Bool) × Proof Scalar Scalar) :=
  transform context historyQuery (importedValidator raw 0 1 handle) initial proof

theorem compiled_premises :
    Pr{let result ← (simulateQ randomOracle (cheater >>= compiledVerifier)).run' ∅}[
      Accepted (· = some true) result.1] ≤ 1 / 5 := by
  have bound := compiled_imported_soundness context compiledVerifier 1 raw table decoded 0
    false_claim handle initial (fun _ => rfl) cheater 0 cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
    using bound

theorem compiled_plain_premises :
    Pr{let result ← (simulateQ randomOracle (cheater >>= fun proof =>
        transform context historyQuery (plain 0) initial proof)).run' ∅}[
      Accepted (· = some true) result.1] ≤ 1 / 5 := by
  have bound := compiled_soundness context _ (plain 0) initial (fun _ => rfl)
    SumcheckSourceVerifier.childContext handle 1 table 0 rfl (by decide +kernel) cheater 0
    cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
    using bound

theorem compiled_adaptive_premises :
    Pr{let result ← (simulateQ randomOracle (adaptiveCheater >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          transform context (decodedQuery (id : Scalar → Scalar))
            (importedValidator claimed.1.raw claimed.1.claim claimed.1.count handle)
            (binding claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤ 2 / 5 := by
  have bound := compiled_adaptive_soundness context handle (id : Scalar → Scalar) 0 balanced_id
    binding binding_determined
    (fun statement proof => transform context (decodedQuery id)
      (importedValidator statement.raw statement.claim statement.count handle)
      (binding statement) proof) (fun _ _ => rfl) adaptiveCheater 0 trivial
  simpa only [Nat.cast_zero, zero_add, add_zero, ZMod.card, Nat.cast_ofNat, mul_one_div]
    using bound

/-- Accepting the Boolean selection `getD false` of the decision output implies
the decision `some true`. -/
theorem selected_reflects (value : Option Bool) (selected : value.getD false = true) :
    value = some true := by
  cases value with
  | none => cases selected
  | some decided => exact congrArg some selected

/-- A compiled verifier read through a Boolean selection of the imported
program's outputs, given by its construction equation. -/
def selectedVerifier (proof : Proof Scalar Scalar) :
    OracleComp (FieldOracle Scalar Scalar) (PIR.Outcome Bool × Proof Scalar Scalar) :=
  transform context historyQuery
    (((SumcheckSourceViews.imported.program.participant Scalar Scalar 1
      (SumcheckSourceVerifier.sourceRootInputs (some raw) (some 0) (some 1) (some handle))).bind
        fun outputs => .done ((outputs.get .here).getD false)).interpret
      Structured.CommonAdapter.project)
    initial proof

/-- All premises of `compiled_participant_soundness` hold together. -/
theorem participant_premises :
    Pr{let result ← (simulateQ randomOracle (cheater >>= selectedVerifier)).run' ∅}[
      Accepted (· = true) result.1] ≤ 1 / 5 := by
  have bound := compiled_participant_soundness context selectedVerifier 1 raw table decoded 0
    false_claim handle initial (fun outputs => (outputs.get .here).getD false) (· = true)
    (fun outputs selected => selected_reflects _ selected) (fun _ => rfl) cheater 0 cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
    using bound

/-! ### Outcome images -/

/-- A compiled verifier's report of the plain verifier's outcome: acceptance
returns unit, and a returned rejection or a missing decision becomes the stop
`reject`. -/
def reportOutcome :
    PIR.Outcome (Option Bool) × Proof Scalar Scalar → PIR.Outcome Unit × Proof Scalar Scalar
  | (.returned (some true), rest) => (.returned (), rest)
  | (.returned _, rest) => (.stopped .reject, rest)
  | (.stopped reason, rest) => (.stopped reason, rest)

theorem reportOutcome_preserves (result : PIR.Outcome (Option Bool) × Proof Scalar Scalar)
    (accepted : Accepted (fun _ : Unit => True) (reportOutcome result).1) :
    Accepted (· = some true) result.1 := by
  obtain ⟨outcome, rest⟩ := result
  cases outcome with
  | returned value =>
    cases value with
    | none => exact False.elim accepted
    | some decided =>
      cases decided
      · exact False.elim accepted
      · rfl
  | stopped reason => exact False.elim accepted

/-- All premises of `acceptance_le_of_image` hold for the reporting verifier;
with the plain verifier's bound its acceptance is at most `1 / 5`. -/
theorem image_premises :
    Pr{let result ← (simulateQ randomOracle (cheater >>= fun proof =>
        reportOutcome <$> transform context historyQuery (plain 0) initial proof)).run' ∅}[
      Accepted (fun _ : Unit => True) result.1] ≤ 1 / 5 := by
  refine (acceptance_le_of_image context (plain 0) initial _ reportOutcome (fun _ => rfl)
    (· = some true) (fun _ => True) reportOutcome_preserves cheater).trans ?_
  have bound := ZkcSecurity.Examples.SumcheckFiatShamir.soundness context
    SumcheckSourceVerifier.childContext handle 1 table 0 (by decide +kernel) initial cheater 0
    cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
    using bound

/-- A report that accepts every outcome, which violates the premise that an
accepted image comes only from an accepted outcome. -/
def acceptAll (result : PIR.Outcome (Option Bool) × Proof Scalar Scalar) :
    PIR.Outcome Unit × Proof Scalar Scalar :=
  (.returned (), result.2)

/-- Without that premise the transfer fails: the report accepting every outcome
accepts the cheating proof with probability one, while the transform accepts it
with probability at most `1 / 5`. -/
theorem acceptAll_certain :
    Pr{let result ← (simulateQ randomOracle (cheater >>= fun proof =>
        acceptAll <$> transform context historyQuery (plain 0) initial proof)).run' ∅}[
      Accepted (fun _ : Unit => True) result.1] = 1 := by
  have imaged : (cheater >>= fun proof =>
      acceptAll <$> transform context historyQuery (plain 0) initial proof) =
        acceptAll <$> experiment context (plain 0) initial cheater := by
    rw [experiment, map_bind]
  have mapped : (simulateQ randomOracle
      (acceptAll <$> experiment context (plain 0) initial cheater)).run' ∅ =
        acceptAll <$>
          (simulateQ randomOracle (experiment context (plain 0) initial cheater)).run' ∅ := by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [imaged, mapped, prEvent_map]
  exact prEvent_true_eq_one _

theorem acceptAll_exceeds :
    ¬ Pr{let result ← (simulateQ randomOracle (cheater >>= fun proof =>
        acceptAll <$> transform context historyQuery (plain 0) initial proof)).run' ∅}[
      Accepted (fun _ : Unit => True) result.1] ≤ 1 / 5 := by
  rw [acceptAll_certain]
  intro bound
  have real := (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (ENNReal.div_ne_top (by simp) (by simp))).mpr bound
  rw [ENNReal.toReal_div] at real
  norm_num at real

/-- The adaptive compiled verifier read through the same Boolean selection. -/
def selectedAdaptive (statement : PublicStatement Scalar) (proof : Proof Scalar Scalar) :
    OracleComp (Oracle Scalar Scalar Scalar) (PIR.Outcome Bool × Proof Scalar Scalar) :=
  transform context (decodedQuery (id : Scalar → Scalar))
    (((SumcheckSourceViews.imported.program.participant Scalar Scalar 1
      (SumcheckSourceVerifier.sourceRootInputs (some statement.raw) (some statement.claim)
        (some statement.count) (some handle))).bind fun outputs =>
          .done ((outputs.get .here).getD false)).interpret Structured.CommonAdapter.project)
    (binding statement) proof

/-- All premises of `compiled_adaptive_participant_soundness` hold together. -/
theorem adaptive_participant_premises :
    Pr{let result ← (simulateQ randomOracle (adaptiveCheater >>= fun claimed =>
        (fun result => (claimed.1, result)) <$> selectedAdaptive claimed.1 claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = true) result.2.1] ≤ 2 / 5 := by
  have bound := compiled_adaptive_participant_soundness context handle (id : Scalar → Scalar) 0
    balanced_id binding binding_determined (fun outputs => (outputs.get .here).getD false)
    (· = true) (fun outputs selected => selected_reflects _ selected) selectedAdaptive
    (fun _ _ => rfl) adaptiveCheater 0 trivial
  simpa only [Nat.cast_zero, zero_add, add_zero, ZMod.card, Nat.cast_ofNat, mul_one_div]
    using bound

/-! ### The Reduction root -/

/-- An external table of dimension `1 + 1` with values `0, 3, 2, 1`, whose sum
is `1`. One round reduces it to a claim on its marginal over the last
coordinate. -/
def wideTable : Table Scalar (1 + 1) := fun bits =>
  if bits 0 then (if bits 1 then 1 else 2) else (if bits 1 then 3 else 0)

theorem wideTable_false : (0 : Scalar) ≠ booleanSum wideTable := by decide +kernel

/-- All premises of `reduction_soundness` hold with one remaining coordinate and
the false claim `0`. -/
theorem reduction_premises :
    Pr{let result ← (simulateQ randomOracle (experiment context
        (importedReduction (G := Scalar) none none 0 1 handle) initial cheater)).run' ∅}[
      Accepted (ZkcSecurity.Examples.CausalSumcheck.SourceVerifier.residualObservation
        (G := Scalar) 1 1 wideTable) result.1] ≤ 1 / 5 := by
  have bound := reduction_soundness context none none 1 1 wideTable 0 wideTable_false handle
    initial cheater 0 cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
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

/-- A cheating prover on the oracle answering samples below `64`. -/
def wideCheater :
    OracleComp (Oracle Scalar Scalar (Fin 64)) (PublicStatement Scalar × Proof Scalar Scalar) :=
  pure (falseStatement, cheat)

/-- All premises of `reduced_imported_soundness` hold together with reduction
from samples below `64`. -/
theorem reduced_imported_premises :
    Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context (reduce numbering 64)
        (fun statement : PublicStatement Scalar =>
          importedValidator statement.raw statement.claim statement.count handle)
        binding wideCheater)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      ((0 : ℕ) + 2) * (1 / 5 + 5 / 64) := by
  have bound := reduced_imported_soundness context handle numbering 64 binding binding_determined
    wideCheater 0 trivial
  simpa only [ZMod.card, Nat.cast_ofNat] using bound

/-- The reduced bound is below one. -/
theorem reduced_bound_below_one : ((0 : ℕ) + 2 : ENNReal) * (1 / 5 + 5 / 64) < 1 := by
  have fifth : (1 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have share : (5 / 64 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  rw [Nat.cast_zero, zero_add, ← ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨fifth, share⟩)) ENNReal.one_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_add fifth share, ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num

end TestsSecurity.SumcheckFiatShamir
