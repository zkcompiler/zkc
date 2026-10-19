module

public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

@[expose] public section

/-! # Keyed bad-event certificates: the probabilistic endpoint

A game is an oracle computation on VCVio's lazily sampled random oracle
`OracleSpec.ofFn R` over any key space `D`: event histories, pairs of a
history and an occurrence, or a joint space of transcript keys and hash calls.
A keyed certificate (`KeyedCertificate`) for an event of the game's result
names a per-key charge and a bad predicate on keys and answer tables, with two
obligations:

- **all-table resampling** (`ResampleBound`): under every table of answers,
  resampling one key's answer makes that key bad with probability at most the
  key's charge;
- **trace**: whenever the game's deterministic run against a total table hits
  the event, the run asks some key that is bad under that table.

`KeyedCertificate.soundness` is the single endpoint theorem: the event's
probability in the empty-cache random-oracle execution is at most any pathwise
bound on the game's weighted queries (`WorstCaseCostBound`), every query
charged its key's charge, repeats and cache hits included. It is VCVio's
weighted bad-query bound
(`OracleComp.prEvent_randomOracle_le_of_bad_queries_weighted`). Interface
certificates reach it through transformers (`Typed.ChargedCertificate.keyed`),
as does the commitment bridge's joint game.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp OracleSpec

variable {D α : Type} {R : D → Type}

/-- The all-table resampling premise: under every background table, resampling
the answer at any key makes the key bad with probability at most its charge. -/
def ResampleBound [DecidableEq D] (R : D → Type) [∀ key, SampleableType (R key)]
    (bad : D → ((key : D) → R key) → Prop) (charge : D → ENNReal) : Prop :=
  ∀ (key : D) (table : (key : D) → R key),
    Pr{let raw ← $ᵗ (R key)}[bad key (Function.update table key raw)] ≤ charge key

/-- A keyed bad-event certificate for the event `fails` of `game`: a per-key
charge and a bad predicate meeting the all-table resampling premise, such that
every run hitting the event asks a bad key. -/
structure KeyedCertificate [DecidableEq D] (R : D → Type) [∀ key, SampleableType (R key)]
    (game : OracleComp (OracleSpec.ofFn R) α) (fails : α → Prop) where
  charge : D → ENNReal
  bad : D → ((key : D) → R key) → Prop
  resample : ResampleBound R bad charge
  trace : ∀ table : (key : D) → R key, fails (evalWithAnswerFn (QueryImpl.ofFn table) game) →
    ∃ query ∈ tableQueryLog game table, bad query.1 table

namespace KeyedCertificate
variable [DecidableEq D] [∀ key, SampleableType (R key)]
  {game : OracleComp (OracleSpec.ofFn R) α} {fails : α → Prop}

/-- The endpoint: the event's probability in the empty-cache random-oracle
execution is at most the game's pathwise weighted query budget, every query
charged its key's charge. -/
theorem soundness (certificate : KeyedCertificate R game fails) {cost : ENNReal}
    (budget : WorstCaseCostBound game ⟨certificate.charge⟩ cost) :
    Pr{let result ← (simulateQ randomOracle game).run' ∅}[fails result] ≤ cost :=
  prEvent_randomOracle_le_of_bad_queries_weighted game certificate.charge cost budget fails
    certificate.bad certificate.resample certificate.trace

/-- A certificate for an event is one for every smaller event. -/
def mono (certificate : KeyedCertificate R game fails) {smaller : α → Prop}
    (implies : ∀ result, smaller result → fails result) : KeyedCertificate R game smaller where
  charge := certificate.charge
  bad := certificate.bad
  resample := certificate.resample
  trace table hit := certificate.trace table (implies _ hit)

/-- A certificate with larger charges. -/
def weaken (certificate : KeyedCertificate R game fails) {larger : D → ENNReal}
    (le : ∀ key, certificate.charge key ≤ larger key) : KeyedCertificate R game fails where
  charge := larger
  bad := certificate.bad
  resample key table := (certificate.resample key table).trans (le key)
  trace := certificate.trace

/-- Private randomness drawn before the oracle computation: when every game in
the support of `games` has a certificate whose charges stay within a common
weighted budget, the mixture inherits the bound. -/
theorem soundness_mixture (games : ProbComp (OracleComp (OracleSpec.ofFn R) α))
    (certificate : ∀ game ∈ support games, KeyedCertificate R game fails) {cost : ENNReal}
    (budget : ∀ game (member : game ∈ support games),
      WorstCaseCostBound game ⟨(certificate game member).charge⟩ cost) :
    Pr{let result ← games >>= fun game => (simulateQ randomOracle game).run' ∅}[fails result] ≤
      cost :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun game member =>
    (certificate game member).soundness (budget game member)

end KeyedCertificate

end ZkcSecurity.FiatShamir
