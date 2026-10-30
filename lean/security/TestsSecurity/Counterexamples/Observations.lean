import ZkcSecurity.Transformations.FiatShamir.Obligations
import ZkcSecurityExamples.CommittedOpening
import TestsSecurity.Counterexamples.Support
import Mathlib.Data.ZMod.Basic

/-! Security attacks on constructions that leave producer data or statement data
out of the transcript.

The group is `ZMod 5 × ZMod 5` with generator `(1, 0)`; a point has a discrete
logarithm exactly when its second coordinate is zero (`inSpan_iff`), so
`falseStatement = (0, 1)` has none. Each attack runs a prover with access to the
lazily sampled oracle, then the flawed verifier in the same oracle, and states
the probability that a false statement is accepted. Each violates an obligation
of the [construction obligations](../../../../../docs/spec/ir/construction-obligations.md).

- **A challenge that omits the commitment.** The Schnorr challenge is the oracle
  at the statement alone; the prover takes the challenge, picks the response
  and solves for the commitment. A false statement is accepted with probability
  one (`scope_acceptance`). The request's key does not determine the commitment
  (`scope_not_determined`), and the ignored first message belongs to no
  omission class (`firstMessage_unclassified`).
- **A binding that omits the statement.** The challenge is the oracle at the
  commitment alone, with challenges decoded to nonzero scalars; the prover
  fixes the commitment and the response and solves for the statement, which is
  then false. Accepted with probability one (`statement_acceptance`); the
  initial history does not determine the statement (`statement_not_determined`).
- **Generators as an unauthenticated runtime parameter.** The generator is not
  absorbed; the prover chooses it after the challenge. A statement without a
  discrete logarithm to the pinned generator is accepted with probability one
  (`generator_acceptance`); the generator is not authenticated configuration
  (`generator_not_authenticated`).
- **An OR-proof challenge share ignored before a later challenge.** The share
  `c₁` is omitted from the key of the batching weight `w`; the prover solves for
  `c₁` after seeing `w`. A false OR statement is accepted with probability
  `21 / 25` (`share_acceptance`); the share is not reconstructible
  (`share_unclassified`).
- **Evaluation claims not observed before batching.** The claims are omitted
  from the batching weight's key; the prover picks false claims that satisfy the
  batched check after seeing the weight. Accepted with probability one
  (`claims_acceptance`); the claims belong to no omission class
  (`claims_unclassified`).
- **An undeclared challenge.** An evaluation point is the oracle at the blob
  alone and is used in arithmetic; the commitment is chosen after it. A
  commitment other than the blob's polynomial is accepted with probability one
  (`undeclared_acceptance`); the challenge's input does not cover the
  commitment the check reads (`undeclared_not_covered`).
- **A free opening position.** A committed table `T i = i` is opened at a position
  the producer sends with the opening, omitted from the transcript, and the
  verifier accepts when the position equals the challenge. Interactively a fixed
  position is accepted with probability `1 / 4` (`interactive_position`); the
  omitting construction accepts with probability one (`free_acceptance`). The
  position is not fixed at the receive point (`free_not_fixed`).
- **A position from an unbound public parameter.** The same verifier with the
  position as a statement input that is not bound: the prover chooses it after
  the challenge, accepted with probability one (`parameter_acceptance`); the
  position is not fixed by the admissible sources (`parameter_not_fixed`).
-/

namespace TestsSecurity.Counterexamples.Observations
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open TestsSecurity.Counterexamples
open ZkcSecurity.Examples.CommittedOpening (prEvent_randomOracle_eq_one)
open scoped ENNReal

abbrev Scalar := ZMod 5
abbrev Group := Scalar × Scalar

def generator : Group := (1, 0)

/-- A point with a discrete logarithm to the generator. -/
def InSpan (point : Group) : Prop := ∃ witness : Scalar, witness • generator = point

theorem inSpan_iff (point : Group) : InSpan point ↔ point.2 = 0 := by
  constructor
  · rintro ⟨witness, rfl⟩
    simp [generator]
  · intro zero
    exact ⟨point.1, Prod.ext (by simp [generator]) (by simp [generator, zero])⟩

/-- A statement with no discrete logarithm. -/
def falseStatement : Group := (0, 1)

theorem falseStatement_false : ¬ InSpan falseStatement := by
  rw [inSpan_iff]
  decide

/-- Transcript events of the flawed constructions. -/
inductive Event where
  | statement (point : Group)
  | commitment (point : Group)
  | values (pair : Scalar × Scalar)
  | blob (pair : Scalar × Scalar)
  | root
  deriving DecidableEq

abbrev Key := List Event

/-! ### A challenge that omits the commitment -/

/-- The flawed key: the statement alone. -/
def scopeKey (statement : Group) : Key := [.statement statement]

def scopeVerifier (statement : Group) (proof : Group × Scalar) :
    OracleComp (Key →ₒ Scalar) Bool := do
  let challenge ← liftM ((Key →ₒ Scalar).query (scopeKey statement))
  pure (decide (proof.2 • generator = proof.1 + challenge • statement))

/-- Take the challenge, answer `0`, and solve for the commitment. -/
def scopeProver (statement : Group) : OracleComp (Key →ₒ Scalar) (Group × Scalar) := do
  let challenge ← liftM ((Key →ₒ Scalar).query (scopeKey statement))
  pure (-(challenge • statement), 0)

def scopeExperiment (statement : Group) : OracleComp (Key →ₒ Scalar) Bool :=
  scopeProver statement >>= scopeVerifier statement

/-- The false statement is accepted with probability one. -/
theorem scope_acceptance :
    Pr{let accepted ← (simulateQ randomOracle (scopeExperiment falseStatement)).run' ∅}[
      accepted = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun table => by
    simp [scopeExperiment, scopeProver, scopeVerifier]

/-- The request's key does not determine the commitment message the check
reads. -/
theorem scope_not_determined :
    ¬ Determines (fun context : Group × Group => scopeKey context.1) (fun context => context.2) :=
  not_determines (first := (falseStatement, 0)) (second := (falseStatement, generator)) rfl
    (by decide)

/-- The ignored first message is neither reconstructible, nor an opening, nor
terminal. -/
theorem firstMessage_unclassified :
    ¬ (Omission.mk (fun context : Group × Group => scopeKey context.1) (fun context => context.2)
      True False).Classified :=
  Omission.not_classified scope_not_determined id trivial

/-! ### A binding that omits the statement -/

/-- A nonzero challenge decoded from four raw values. -/
def nonzero (raw : Fin 4) : Scalar := (raw.val + 1 : ℕ)

/-- A commitment with no discrete logarithm. -/
def offCommitment : Group := (0, 1)

def statementVerifier (statement : Group) (proof : Group × Scalar) :
    OracleComp (Key →ₒ Fin 4) Bool := do
  let raw ← liftM ((Key →ₒ Fin 4).query [.commitment proof.1])
  pure (decide (proof.2 • generator = proof.1 + nonzero raw • statement))

/-- Fix the commitment and the response `0`, take the challenge, and solve for
the statement. -/
def statementProver : OracleComp (Key →ₒ Fin 4) (Group × (Group × Scalar)) := do
  let raw ← liftM ((Key →ₒ Fin 4).query [.commitment offCommitment])
  pure (-((nonzero raw)⁻¹ • offCommitment), (offCommitment, 0))

def statementExperiment : OracleComp (Key →ₒ Fin 4) (Group × Bool) :=
  statementProver >>= fun claimed => (claimed.1, ·) <$> statementVerifier claimed.1 claimed.2

/-- Every raw challenge makes the solved statement false and accepted. -/
theorem statement_solved (raw : Fin 4) :
    ¬ InSpan (-((nonzero raw)⁻¹ • offCommitment)) ∧
      decide ((0 : Scalar) • generator =
        offCommitment + nonzero raw • -((nonzero raw)⁻¹ • offCommitment)) = true := by
  rw [inSpan_iff]
  revert raw
  decide +kernel

/-- A false statement chosen after the challenge is accepted with probability
one. -/
theorem statement_acceptance :
    Pr{let result ← (simulateQ randomOracle statementExperiment).run' ∅}[
      ¬ InSpan result.1 ∧ result.2 = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun table => by
    simp only [statementExperiment, statementProver, statementVerifier, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure, evalWithAnswerFn_map]
    exact statement_solved _

/-- The initial history omits the statement, so it does not determine it. -/
theorem statement_not_determined : ¬ Typed.Determined (fun _ : Group => ([] : List Event)) := by
  intro determined
  exact absurd (determined falseStatement 0 [] [] rfl) (by decide)

/-! ### Generators as an unauthenticated runtime parameter -/

def generatorKey (statement commitment : Group) : Key := [.statement statement, .commitment commitment]

/-- The verifier uses the generator the proof carries, which is not absorbed. -/
def generatorVerifier (statement : Group) (proof : Group × Group × Scalar) :
    OracleComp (Key →ₒ Scalar) Bool := do
  let challenge ← liftM ((Key →ₒ Scalar).query (generatorKey statement proof.2.1))
  pure (decide (proof.2.2 • proof.1 = proof.2.1 + challenge • statement))

/-- Commit to zero, take the challenge, and choose the generator. -/
def generatorProver (statement : Group) : OracleComp (Key →ₒ Scalar) (Group × Group × Scalar) := do
  let challenge ← liftM ((Key →ₒ Scalar).query (generatorKey statement 0))
  pure (challenge • statement, 0, 1)

def generatorExperiment (statement : Group) : OracleComp (Key →ₒ Scalar) Bool :=
  generatorProver statement >>= generatorVerifier statement

/-- A statement without a discrete logarithm to the pinned generator is accepted
with probability one. -/
theorem generator_acceptance :
    Pr{let accepted ← (simulateQ randomOracle (generatorExperiment falseStatement)).run' ∅}[
      accepted = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun table => by
    simp [generatorExperiment, generatorProver, generatorVerifier]

/-- The generator the verifier uses varies with the proof: it is not
authenticated configuration. -/
theorem generator_not_authenticated :
    ¬ AuthenticatedConfiguration (fun proof : Group × Group × Scalar => proof.1) :=
  fun authenticated => absurd (authenticated (generator, 0, 0) (0, 0, 0)) (by decide)

/-! ### An OR-proof challenge share ignored before a later challenge -/

/-- The keys of the two challenges: the first absorbs both commitments, the
batching weight also absorbs both responses but not the share `c₁`. -/
inductive OrKey where
  | first (commitments : Group × Group)
  | second (commitments : Group × Group) (responses : Scalar × Scalar)
  deriving DecidableEq, Fintype

/-- Both branches are false: neither point has a discrete logarithm. -/
def branches : Group × Group := (falseStatement, falseStatement)

/-- The batched check of both branch equations, with `c₀ = c - c₁`. -/
def batched (challenge weight share : Scalar) (commitments : Group × Group)
    (responses : Scalar × Scalar) : Bool :=
  decide (responses.1 • generator - commitments.1 - (challenge - share) • branches.1 +
    weight • (responses.2 • generator - commitments.2 - share • branches.2) = 0)

def shareVerifier (proof : (Group × Group) × Scalar × (Scalar × Scalar)) :
    OracleComp (OrKey →ₒ Scalar) Bool := do
  let challenge ← liftM ((OrKey →ₒ Scalar).query (.first proof.1))
  let weight ← liftM ((OrKey →ₒ Scalar).query (.second proof.1 proof.2.2))
  pure (batched challenge weight proof.2.1 proof.1 proof.2.2)

/-- The share solved after the weight. -/
def solvedShare (challenge weight : Scalar) : Scalar :=
  if weight = 1 then 0 else challenge * (1 - weight)⁻¹

/-- Commit to zeros, respond with zeros, take both challenges, and solve for the
share. -/
def shareProver : OracleComp (OrKey →ₒ Scalar) ((Group × Group) × Scalar × (Scalar × Scalar)) := do
  let challenge ← liftM ((OrKey →ₒ Scalar).query (.first (0, 0)))
  let weight ← liftM ((OrKey →ₒ Scalar).query (.second (0, 0) (0, 0)))
  pure ((0, 0), solvedShare challenge weight, (0, 0))

def shareExperiment : OracleComp (OrKey →ₒ Scalar) Bool := shareProver >>= shareVerifier

theorem branches_false : ¬ InSpan branches.1 ∧ ¬ InSpan branches.2 :=
  ⟨falseStatement_false, falseStatement_false⟩

/-- The solved share passes the batched check unless the weight is `1` and the
first challenge is nonzero. -/
theorem solvedShare_batched (challenge weight : Scalar) :
    batched challenge weight (solvedShare challenge weight) (0, 0) (0, 0) = true ↔
      (weight ≠ 1 ∨ challenge = 0) := by
  revert challenge weight
  decide +kernel

/-- The false OR statement is accepted with probability `21 / 25`. -/
theorem share_acceptance :
    Pr{let accepted ← (simulateQ randomOracle shareExperiment).run' ∅}[accepted = true] = 21 / 25 := by
  refine (prEvent_randomOracle_two _ _ (first := .first (0, 0)) (second := .second (0, 0) (0, 0))
    (by decide) (fun pair => pair.2 ≠ 1 ∨ pair.1 = 0) fun table => by
      simp only [shareExperiment, shareProver, shareVerifier, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
      exact solvedShare_batched _ _).trans ?_
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun pair : Scalar × Scalar => pair.2 ≠ 1 ∨ pair.1 = 0).card = 21 := by
    decide
  rw [count, Fintype.card_prod, ZMod.card]
  numerals

/-- The share is a producer value: the weight's key does not determine it, and a
request follows it. -/
theorem share_unclassified :
    ¬ (Omission.mk (fun context : OrKey × Scalar => context.1) (fun context => context.2)
      True False).Classified :=
  Omission.not_classified (not_determines (first := (.first (0, 0), 0))
    (second := (.first (0, 0), 1)) rfl (by decide)) id trivial

/-! ### Evaluation claims not observed before batching -/

/-- The batching weight's key absorbs the statement's values but not the claims. -/
def claimsKey (values : Scalar × Scalar) : Key := [.values values]

def claimsVerifier (values : Scalar × Scalar) (claims : Scalar × Scalar) :
    OracleComp (Key →ₒ Scalar) Bool := do
  let weight ← liftM ((Key →ₒ Scalar).query (claimsKey values))
  pure (decide (claims.1 + weight * claims.2 = values.1 + weight * values.2))

/-- Take the weight and pick false claims that pass the batched check. -/
def claimsProver (values : Scalar × Scalar) : OracleComp (Key →ₒ Scalar) (Scalar × Scalar) := do
  let weight ← liftM ((Key →ₒ Scalar).query (claimsKey values))
  pure (values.1 + weight, values.2 - 1)

def claimsExperiment (values : Scalar × Scalar) : OracleComp (Key →ₒ Scalar) ((Scalar × Scalar) × Bool) :=
  claimsProver values >>= fun claims => (claims, ·) <$> claimsVerifier values claims

/-- False claims are accepted with probability one. -/
theorem claims_acceptance (values : Scalar × Scalar) :
    Pr{let result ← (simulateQ randomOracle (claimsExperiment values)).run' ∅}[
      result.1 ≠ values ∧ result.2 = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun table => by
    simp only [claimsExperiment, claimsProver, claimsVerifier, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure, evalWithAnswerFn_map]
    refine ⟨fun same => ?_, ?_⟩
    · have second := congrArg Prod.snd same
      simp only [sub_eq_self] at second
      exact absurd second (by decide)
    · exact decide_eq_true (by ring)

theorem scalar_zero_ne_one : (0 : Scalar) ≠ 1 := by decide

/-- The claims are neither reconstructible, nor openings, nor terminal. -/
theorem claims_unclassified (values : Scalar × Scalar) :
    ¬ (Omission.mk (fun _ : Scalar × Scalar => claimsKey values) id True False).Classified :=
  Omission.not_classified (not_determines (first := (0, 0)) (second := (0, 1)) rfl
    (fun same => scalar_zero_ne_one (congrArg Prod.snd same))) id trivial

/-! ### An undeclared challenge -/

/-- A polynomial of degree below two, by its coefficients. -/
def evaluate (polynomial : Scalar × Scalar) (point : Scalar) : Scalar :=
  polynomial.1 + polynomial.2 * point

/-- The evaluation point is the oracle at the blob alone. -/
def undeclaredVerifier (blob : Scalar × Scalar) (commitment : Scalar × Scalar) :
    OracleComp (Key →ₒ Scalar) Bool := do
  let point ← liftM ((Key →ₒ Scalar).query [.blob blob])
  pure (decide (evaluate commitment point = evaluate blob point))

/-- Take the point, then commit to another polynomial that agrees there. -/
def undeclaredProver (blob : Scalar × Scalar) : OracleComp (Key →ₒ Scalar) (Scalar × Scalar) := do
  let point ← liftM ((Key →ₒ Scalar).query [.blob blob])
  pure (blob.1 - point, blob.2 + 1)

def undeclaredExperiment (blob : Scalar × Scalar) :
    OracleComp (Key →ₒ Scalar) ((Scalar × Scalar) × Bool) :=
  undeclaredProver blob >>= fun commitment => (commitment, ·) <$> undeclaredVerifier blob commitment

/-- A commitment that is not the blob's polynomial is accepted with probability
one. -/
theorem undeclared_acceptance (blob : Scalar × Scalar) :
    Pr{let result ← (simulateQ randomOracle (undeclaredExperiment blob)).run' ∅}[
      result.1 ≠ blob ∧ result.2 = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun table => by
    simp only [undeclaredExperiment, undeclaredProver, undeclaredVerifier, evaluate,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure,
      evalWithAnswerFn_map]
    refine ⟨fun same => ?_, ?_⟩
    · have second := congrArg Prod.snd same
      simp only [add_eq_left] at second
      exact absurd second (by decide)
    · exact decide_eq_true (by ring)

/-- The check reads the commitment, which the challenge's input does not cover. -/
theorem undeclared_not_covered :
    ¬ CoveredByInput (fun context : (Scalar × Scalar) × (Scalar × Scalar) => context.1)
      (fun context => context.2) :=
  not_determines (first := (0, 0)) (second := (0, (0, 1))) rfl (by decide)

/-! ### A free opening position and an unbound position parameter -/

/-- The committed table `T i = i`, read at the ideal interpretation. -/
def table (position : Fin 4) : Fin 4 := position

/-- A fixed position chosen before the challenge is accepted with probability
`1 / 4`. -/
theorem interactive_position (position : Fin 4) :
    Pr{let challenge ← $ᵗ (Fin 4)}[position = challenge] = 1 / 4 := by
  rw [prEvent_congr _ _ (fun challenge => challenge = position) fun _ => eq_comm,
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  numerals

/-- The verifier authenticates the row against the committed table and accepts
when the opened position equals the challenge; the opening is not absorbed. -/
def openingVerifier (opening : Fin 4 × Fin 4) : OracleComp (Key →ₒ Fin 4) Bool := do
  let challenge ← liftM ((Key →ₒ Fin 4).query [.root])
  pure (decide (opening.2 = table opening.1 ∧ opening.1 = challenge))

/-- Take the challenge and open the table there. -/
def freeProver : OracleComp (Key →ₒ Fin 4) (Fin 4 × Fin 4) := do
  let challenge ← liftM ((Key →ₒ Fin 4).query [.root])
  pure (challenge, table challenge)

def freeExperiment : OracleComp (Key →ₒ Fin 4) Bool := freeProver >>= openingVerifier

theorem free_acceptance :
    Pr{let accepted ← (simulateQ randomOracle freeExperiment).run' ∅}[accepted = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun answers => by
    simp [freeExperiment, freeProver, openingVerifier, table]

/-- The position comes from the received message, not from the absorbed
history at the receive point. -/
theorem free_not_fixed :
    ¬ FixedAtReceivePoint (fun _ : Fin 4 × Fin 4 => ([.root] : Key)) (fun opening => opening.1) :=
  not_determines (first := (0, 0)) (second := (1, 1)) rfl (by decide)

/-- The position is a public statement input that the transcript does not bind;
the prover chooses it after the challenge. -/
def parameterVerifier (position : Fin 4) (row : Fin 4) : OracleComp (Key →ₒ Fin 4) Bool :=
  openingVerifier (position, row)

def parameterExperiment : OracleComp (Key →ₒ Fin 4) Bool := do
  let challenge ← liftM ((Key →ₒ Fin 4).query [.root])
  parameterVerifier challenge (table challenge)

theorem parameter_acceptance :
    Pr{let accepted ← (simulateQ randomOracle parameterExperiment).run' ∅}[accepted = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun answers => by
    simp [parameterExperiment, parameterVerifier, openingVerifier, table]

/-- A value merely visible to both roles is not an admissible source: the
absorbed history does not fix the position. -/
theorem parameter_not_fixed :
    ¬ FixedAtReceivePoint (fun _ : Fin 4 => ([.root] : Key)) id :=
  not_determines (first := 0) (second := 1) rfl (by decide)

end TestsSecurity.Counterexamples.Observations
