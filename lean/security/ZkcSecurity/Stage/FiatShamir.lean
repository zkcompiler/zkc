module

public import ZkcSecurity.Stage.Relation
public import ZkcSecurity.FiatShamir.Soundness
public import ZkcSecurity.FiatShamir.Typed
public import ZkcSecurity.VCVio.Pruning

@[expose] public section

/-! # Fiat–Shamir stages as stage relations

Games whose bad probability is an event of a random-oracle experiment
(`oracleGame`), and the stages of the Fiat–Shamir path as relations between
them:

- **construction and projection equality and executable pruning**
  (`Relation.ofPrunesImage`, `Relation.ofImage`): a target experiment that
  prunes, or equals, an outcome image of a source experiment is bounded by it
  with the identity translation, the identity budget map and no loss; this is
  the transport lemma `ZkcSecurity.VCVio.Pruning.prEvent_le_of_prunes_image`
  read as a stage;
- **the typed Fiat–Shamir theorem** (`typedRelation`, `chargedRelation`,
  `weightedRelation`): the adaptive typed experiment is bounded from the
  trivial game, with the loss `(q + budget) · bound` at `q` prover queries, or
  `q · bound + validatorCost` for a charged certificate whose key charges are at
  most `bound`, or `c + validatorCost` at a prover's pathwise weighted budget
  `c`.

A per-site improvement needs the weighted budget: against a total query budget
`q` the prover can concentrate its queries on the worst site, so its
contribution stays `q · bound`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Stage
open OracleComp OracleSpec ZkcSecurity.FiatShamir

section Oracle
variable {D α β : Type} [DecidableEq D] {R : D → Type} [∀ key, SampleableType (R key)]

/-- The random-oracle game of an experiment: an adversary's bad probability is
the probability of `event` when its experiment runs against the lazily sampled
random oracle from the empty cache. -/
noncomputable def oracleGame (R : D → Type) [∀ key, SampleableType (R key)] (Adversary Budget : Type)
    (Admissible : Budget → Adversary → Prop)
    (experiment : Adversary → OracleComp (OracleSpec.ofFn R) α) (event : α → Prop) : Game where
  Adversary := Adversary
  Budget := Budget
  Admissible := Admissible
  bad adversary := Pr{let result ← (simulateQ randomOracle (experiment adversary)).run' ∅}[event result]

/-- A target experiment that prunes an outcome image of the source experiment, by
results its event excludes, is a zero-loss stage with the identity translation
and budget map. -/
noncomputable def Relation.ofPrunesImage {Adversary Budget : Type}
    (Admissible : Budget → Adversary → Prop)
    (source : Adversary → OracleComp (OracleSpec.ofFn R) α)
    (target : Adversary → OracleComp (OracleSpec.ofFn R) β) (image : α → β)
    {rejects event : β → Prop} {sourceEvent : α → Prop}
    (disjoint : ∀ result, rejects result → ¬ event result)
    (preserves : ∀ result, event (image result) → sourceEvent result)
    (pruned : ∀ adversary, Zkc.Executable.Prunes rejects (target adversary) (image <$> source adversary)) :
    Relation (oracleGame R Adversary Budget Admissible source sourceEvent)
      (oracleGame R Adversary Budget Admissible target event) :=
  Relation.ofLe (S := oracleGame R Adversary Budget Admissible source sourceEvent)
    (T := oracleGame R Adversary Budget Admissible target event) (fun adversary => adversary)
    (fun budget => budget) (fun _ _ holds => holds) fun _ adversary _ =>
      ZkcSecurity.VCVio.Pruning.prEvent_le_of_prunes_image randomOracle image disjoint preserves
        (pruned adversary) ∅

/-- A target experiment that is an outcome image of the source experiment is a
zero-loss stage: exact compilation equalities. -/
noncomputable def Relation.ofImage {Adversary Budget : Type}
    (Admissible : Budget → Adversary → Prop)
    (source : Adversary → OracleComp (OracleSpec.ofFn R) α)
    (target : Adversary → OracleComp (OracleSpec.ofFn R) β) (image : α → β)
    {event : β → Prop} {sourceEvent : α → Prop}
    (preserves : ∀ result, event (image result) → sourceEvent result)
    (exact : ∀ adversary, target adversary = image <$> source adversary) :
    Relation (oracleGame R Adversary Budget Admissible source sourceEvent)
      (oracleGame R Adversary Budget Admissible target event) :=
  Relation.ofPrunesImage Admissible source target image (rejects := fun _ => False)
    (fun _ => False.elim) preserves fun adversary => exact adversary ▸ Zkc.Executable.Prunes.refl _

end Oracle

section Typed
variable {I : PIR.Signature} {E P A Stmt : Type} {Raw : E → Type} {R : List E → Type}
  [DecidableEq E] [Typed.ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)]
  [∀ event, SampleableType (Raw event)]

/-- The adaptive typed Fiat–Shamir game: provers are oracle computations on the
history oracle that output a statement and a proof, admissible at `q` with at
most `q` queries on every path; the bad event is a false statement's
acceptance. -/
noncomputable def typedGame (absorb : Typed.Interface I E P Raw) (validator : Stmt → PIR.Process I A)
    (initial : Stmt → List E) (falseStatement : Stmt → Prop) (accepts : A → Prop) : Game :=
  oracleGame R (OracleComp (OracleSpec.ofFn R) (Stmt × List P)) ℕ
    (fun queries prover => IsTotalQueryBound prover queries)
    (Typed.experiment absorb validator initial)
    fun result => falseStatement result.1 ∧ Accepted accepts result.2.1

/-- The adaptive typed game with weighted budgets: a prover is admissible at `c`
when its queries charge at most `c` on every path, every key charged
`keyCharge charge`. -/
noncomputable def weightedGame (absorb : Typed.Interface I E P Raw) (charge : List E → E → ENNReal)
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E) (falseStatement : Stmt → Prop)
    (accepts : A → Prop) : Game :=
  oracleGame R (OracleComp (OracleSpec.ofFn R) (Stmt × List P)) ENNReal
    (fun cost prover => WorstCaseCostBound prover ⟨Typed.keyCharge charge⟩ cost)
    (Typed.experiment absorb validator initial)
    fun result => falseStatement result.1 ∧ Accepted accepts result.2.1

/-- The typed Fiat–Shamir theorem with an error per site at most `bound`, as a
stage from the trivial game: loss `(q + budget) · bound` at `q` prover
queries. -/
noncomputable def typedRelation {absorb : Typed.Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Typed.Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound) (validator : Stmt → PIR.Process I A)
    (initial : Stmt → List E) (determined : Typed.Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, Typed.QueryBound absorb (validator statement) budget) :
    Relation Game.trivial (typedGame (R := R) absorb validator initial falseStatement accepts) :=
  Relation.ofBound _ (fun (queries : ℕ) => (queries + budget) * bound)
    fun (queries : ℕ) prover admissible =>
    Typed.adaptive_soundness certificate bounded validator initial determined falseStatement
      doomedValidator budget validatorBound prover queries admissible

/-- The charged typed Fiat–Shamir theorem as a stage from the trivial game, at
total query budgets: when every key's charge is at most `bound`, loss
`q · bound + validatorCost` at `q` prover queries. -/
noncomputable def chargedRelation {absorb : Typed.Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : Typed.ChargedCertificate absorb accepts charge)
    {bound : ENNReal} (bounded : ∀ history event, charge history event ≤ bound)
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E) (determined : Typed.Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (initial statement) (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement,
      Typed.ChargedCostBound absorb charge (validator statement) (initial statement) validatorCost) :
    Relation Game.trivial (typedGame (R := R) absorb validator initial falseStatement accepts) :=
  Relation.ofBound _ (fun (queries : ℕ) => queries * bound + validatorCost)
    fun (queries : ℕ) prover admissible =>
    Typed.adaptive_soundness_charged certificate validator initial determined falseStatement
      doomedValidator validatorCost validatorBound prover (queries * bound)
      (Typed.worstCaseCostBound_of_isTotalQueryBound _ (Typed.keyCharge_le bounded) prover queries
        admissible)

/-- The charged typed Fiat–Shamir theorem at weighted budgets, as a stage from the
trivial game: loss `c + validatorCost` at a prover's weighted budget `c`. -/
noncomputable def weightedRelation {absorb : Typed.Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : Typed.ChargedCertificate absorb accepts charge)
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E) (determined : Typed.Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (initial statement) (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement,
      Typed.ChargedCostBound absorb charge (validator statement) (initial statement) validatorCost) :
    Relation Game.trivial
      (weightedGame (R := R) absorb charge validator initial falseStatement accepts) :=
  Relation.ofBound _ (fun (cost : ENNReal) => cost + validatorCost)
    fun (cost : ENNReal) prover admissible =>
    Typed.adaptive_soundness_charged certificate validator initial determined falseStatement
      doomedValidator validatorCost validatorBound prover cost admissible

end Typed

end ZkcSecurity.Stage
