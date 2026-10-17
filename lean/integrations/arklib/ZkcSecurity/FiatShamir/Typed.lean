module

public import ZkcSecurity.FiatShamir.Interface

@[expose] public section

/-! Fiat–Shamir soundness over typed query sites, with an error per site.

The ideal experiment is the one of `ZkcSecurity.FiatShamir.Soundness`, over any
transcript interface: a prover makes arbitrary adaptive queries to a lazily
sampled random oracle on all event histories, starting from an empty cache, and
outputs a statement and a proof; the transform of that statement's validator
answers each of its queries with the same oracle at the history ending with the
query's occurrence. Every query of the whole execution counts, including
repeated and cached ones.

A certificate (`Certificate`) is a doomed set of residual validator processes
that received and sent messages cannot leave and that contains no accepting
result. From a doomed query, the site's own decoding of a fresh uniform oracle
answer leaves the doomed set with probability at most the error of the query's
absorbed occurrence. The escape bound is stated for the decoded law of each
site, so sampling corrections are part of the site's error: a decoding that
inflates every point probability by at most a factor multiplies the site's
uniform-law error by that factor, and an additive loss adds to it (see
`ZkcSecurity.FiatShamir.Sampling`).

`adaptive_soundness_weighted` charges every oracle key the error of its last
event. If the prover's queries charge at most `proverCost` on every path and
every validator's queries at most `validatorCost`, a false statement is accepted
with probability at most `proverCost + validatorCost`. With all errors at most
`bound`, `queries` prover queries and `budget` validator queries this is
`(queries + budget) * bound` (`adaptive_soundness`). `soundness_weighted` and
`soundness` are the fixed-statement forms; `randomized_soundness` adds private
randomness drawn before the oracle computation.

The proof applies VCVio's weighted adaptive bad-query bound
(`OracleComp.prEvent_randomOracle_le_of_bad_queries_weighted`) directly to the
history oracle. A key is bad when replaying a statement's validator along the
key reaches a doomed query whose occurrence is the key's last event and whose
decoded answer at the key leaves the doomed set. Replay reads the oracle only
at shorter histories and the key determines the statement, so resampling the
key's answer leaves the replayed residual unchanged; an accepting run from a
doomed validator must leave the doomed set at one of its own queries, which are
in the query log.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Typed
open OracleComp OracleSpec

variable {I : PIR.Signature} {E P B A Stmt : Type}

section Certificate
variable [SampleableType B]

/-- The local obligation of a doomed set at one residual: a doomed result does
not accept, doomed receives and sends stay doomed, and a doomed query leaves the
doomed set under its decoded fresh answer with probability at most the error of
its occurrence. -/
def Step (absorb : Interface I E P B) (doomed : PIR.Proc I A → Prop) (accepts : A → Prop)
    (error : E → ENNReal) : PIR.Proc I A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call operation next =>
      match absorb operation with
      | .receive _ _ => ∀ value, doomed (next value)
      | .send _ value => doomed (next value)
      | .query event decode =>
          Pr{let reply ← $ᵗ B}[¬ doomed (next (decode reply))] ≤ error event
      | .refuse => True

/-- Round-by-round soundness over a transcript interface, with an error per
absorbed query occurrence: a doomed set of residual processes whose every
member meets its local obligation `Step`. -/
structure Certificate (absorb : Interface I E P B) (accepts : A → Prop) (error : E → ENNReal) where
  doomed : PIR.Proc I A → Prop
  step : ∀ process, doomed process → Step absorb doomed accepts error process

variable (absorb : Interface I E P B)

/-- Enlarging the doomed set keeps every local obligation. -/
theorem Step.mono {accepts : A → Prop} {error : E → ENNReal}
    {small large : PIR.Proc I A → Prop} (included : ∀ process, small process → large process) :
    ∀ process, Step absorb small accepts error process → Step absorb large accepts error process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Step, absorbed] at step ⊢
        exact fun value => included _ (step value)
      · simp only [Step, absorbed] at step ⊢
        exact included _ step
      · simp only [Step, absorbed] at step ⊢
        exact (prEvent_mono _ _ (fun reply => ¬ small (next (decode reply)))
          (fun _ outside inside => outside (included _ inside))).trans step
      · simp only [Step, absorbed]

/-- Larger errors keep every local obligation. -/
theorem Step.mono_error {doomed : PIR.Proc I A → Prop} {accepts : A → Prop}
    {error larger : E → ENNReal} (le : ∀ event, error event ≤ larger event) :
    ∀ process, Step absorb doomed accepts error process → Step absorb doomed accepts larger process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Step, absorbed] at step ⊢
        exact step
      · simp only [Step, absorbed] at step ⊢
        exact step
      · simp only [Step, absorbed] at step ⊢
        exact step.trans (le event)
      · simp only [Step, absorbed]

/-- A certificate with larger errors. -/
def Certificate.weaken {accepts : A → Prop} {error larger : E → ENNReal}
    (certificate : Certificate absorb accepts error) (le : ∀ event, error event ≤ larger event) :
    Certificate absorb accepts larger where
  doomed := certificate.doomed
  step process member := Step.mono_error absorb le process (certificate.step process member)

end Certificate

section Bad
variable [DecidableEq E]

/-- The answer `reply` to a doomed query whose occurrence is `observed` leaves
the doomed set. Only query nodes can escape. -/
def Escapes (absorb : Interface I E P B) (doomed : PIR.Proc I A → Prop) :
    PIR.Proc I A → E → B → Prop
  | .call operation next, observed, reply =>
      match absorb operation with
      | .query event decode =>
          observed = event ∧ doomed (.call operation next) ∧ ¬ doomed (next (decode reply))
      | _ => False
  | _, _, _ => False

/-- A bad oracle key: for some statement, replaying its validator from its
initial history along the key's events before the last one reaches a residual
whose query, answered by the table at the key, escapes the doomed set. -/
def BadKey (absorb : Interface I E P B) (doomed : PIR.Proc I A → Prop)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (key : List E)
    (table : List E → B) : Prop :=
  ∃ statement events observed process, key = initial statement ++ events ++ [observed] ∧
    replay absorb table (validator statement) (initial statement) events = some process ∧
    Escapes absorb doomed process observed (table key)

theorem update_agrees (table : List E → B) (initial events : List E) (observed : E) (reply : B) :
    ∀ other : List E, other.length ≤ initial.length + events.length →
      Function.update table (initial ++ events ++ [observed]) reply other = table other := by
  intro other bound
  apply Function.update_of_ne
  intro same
  rw [same] at bound
  simp at bound

omit [DecidableEq E] in
/-- Two decompositions of one key agree. -/
theorem key_shape {initial events events' : List E} {observed observed' : E}
    (same : initial ++ events ++ [observed] = initial ++ events' ++ [observed']) :
    events = events' ∧ observed = observed' := by
  rw [List.append_assoc, List.append_assoc] at same
  obtain ⟨prefixes, lasts⟩ := List.append_inj' (List.append_cancel_left same) rfl
  exact ⟨prefixes, List.singleton_inj.mp lasts⟩

/-- The replayed residual before a key does not depend on the answer at the key. -/
theorem replay_update (absorb : Interface I E P B) (table : List E → B)
    (validator : PIR.Proc I A) (initial events : List E) (observed : E) (reply : B) :
    replay absorb (Function.update table (initial ++ events ++ [observed]) reply) validator
        initial events =
      replay absorb table validator initial events :=
  replay_congr absorb _ events validator initial
    (fun other bound => update_agrees table initial events observed reply other bound)

variable [SampleableType B]

omit [DecidableEq E] in
/-- A fixed residual escapes at a fresh uniform answer with probability at most
the error of the occurrence. -/
theorem escapes_le {absorb : Interface I E P B} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Certificate absorb accepts error) (process : PIR.Proc I A) (observed : E) :
    Pr{let reply ← $ᵗ B}[Escapes absorb certificate.doomed process observed reply] ≤
      error observed := by
  classical
  have impossible : (∀ reply, ¬ Escapes absorb certificate.doomed process observed reply) →
      Pr{let reply ← $ᵗ B}[Escapes absorb certificate.doomed process observed reply] ≤
        error observed :=
    fun never => (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le
  cases process with
  | done value => exact impossible fun _ escapes => escapes
  | halt stop => exact impossible fun _ escapes => escapes
  | call operation next =>
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · exact impossible fun _ escapes => by simp only [Escapes, absorbed] at escapes
      · exact impossible fun _ escapes => by simp only [Escapes, absorbed] at escapes
      · by_cases relevant : observed = event ∧ certificate.doomed (.call operation next)
        · obtain ⟨rfl, doomed⟩ := relevant
          have step := certificate.step _ doomed
          simp only [Step, absorbed] at step
          refine (prEvent_mono _ _ (fun reply => ¬ certificate.doomed (next (decode reply)))
            (fun reply escapes => ?_)).trans step
          simp only [Escapes, absorbed] at escapes
          exact escapes.2.2
        · exact impossible fun reply escapes => by
            simp only [Escapes, absorbed] at escapes
            exact relevant ⟨escapes.1, escapes.2.1⟩
      · exact impossible fun _ escapes => by simp only [Escapes, absorbed] at escapes

/-- Resampling the answer at any key, under every background table, makes the
key bad with probability at most the error of its last event. -/
theorem badKey_resample {absorb : Interface I E P B} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Certificate absorb accepts error) (validator : Stmt → PIR.Proc I A)
    (initial : Stmt → List E) (determined : Determined initial) (key : List E)
    (table : List E → B) :
    Pr{let reply ← $ᵗ B}[BadKey absorb certificate.doomed validator initial key
      (Function.update table key reply)] ≤ keyError error key := by
  by_cases found : ∃ statement events observed process,
      key = initial statement ++ events ++ [observed] ∧
      replay absorb table (validator statement) (initial statement) events = some process
  · obtain ⟨statement, events, observed, process, shape, replayed⟩ := found
    subst shape
    have reduced : ∀ reply,
        BadKey absorb certificate.doomed validator initial
            (initial statement ++ events ++ [observed])
            (Function.update table (initial statement ++ events ++ [observed]) reply) →
          Escapes absorb certificate.doomed process observed reply := by
      rintro reply ⟨statement', events', observed', process', shape', replayed', escapes⟩
      have same : statement = statement' := determined _ _ (events ++ [observed])
        (events' ++ [observed']) (by simpa only [List.append_assoc] using shape')
      subst same
      obtain ⟨rfl, rfl⟩ := key_shape shape'
      rw [replay_update, replayed] at replayed'
      cases replayed'
      simpa using escapes
    calc Pr{let reply ← $ᵗ B}[BadKey absorb certificate.doomed validator initial
            (initial statement ++ events ++ [observed])
            (Function.update table (initial statement ++ events ++ [observed]) reply)]
        ≤ Pr{let reply ← $ᵗ B}[Escapes absorb certificate.doomed process observed reply] :=
          prEvent_mono _ _ _ reduced
      _ ≤ error observed := escapes_le certificate process observed
      _ = keyError error (initial statement ++ events ++ [observed]) :=
          (keyError_append_singleton error _ observed).symm
  · have never : ∀ reply, ¬ BadKey absorb certificate.doomed validator initial key
        (Function.update table key reply) := by
      rintro reply ⟨statement, events, observed, process, shape, replayed, _⟩
      subst shape
      rw [replay_update] at replayed
      exact found ⟨statement, events, observed, process, rfl, replayed⟩
    exact (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le

omit [SampleableType B] in
/-- An accepting run of the transform, against a total table, from a doomed
residual reached by replay queries a bad key. -/
theorem escape_logged {absorb : Interface I E P B} {accepts : A → Prop} {error : E → ENNReal}
    [SampleableType B] (certificate : Certificate absorb accepts error)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (table : List E → B)
    (statement : Stmt) :
    ∀ (process : PIR.Proc I A) (events history : List E) (proof : List P),
      replay absorb table (validator statement) (initial statement) events = some process →
      history = initial statement ++ events →
      certificate.doomed process →
      Accepted accepts (transform (m := Id) absorb table process history proof).1 →
      ∃ query ∈ tableQueryLog (transform absorb answer process history proof) table,
        BadKey absorb certificate.doomed validator initial query.1 table := by
  intro process
  induction process with
  | done value =>
      intro events history proof _ _ doomed accepted
      exact absurd accepted (certificate.step _ doomed)
  | halt stop =>
      intro events history proof _ _ _ accepted
      exact accepted.elim
  | call operation next ih =>
      intro events history proof replayed shape doomed accepted
      have step := certificate.step _ doomed
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Step, absorbed] at step
        cases proof with
        | nil =>
            rw [transform_receive_nil absorb _ absorbed] at accepted
            exact accepted.elim
        | cons message rest =>
            rw [transform_receive absorb _ absorbed] at accepted
            rw [transform_receive absorb _ absorbed]
            cases recovered : recover (event message) with
            | none =>
                rw [recovered] at accepted
                exact accepted.elim
            | some value =>
                rw [recovered] at accepted
                dsimp only at accepted ⊢
                apply ih value (events ++ [event message]) _ rest _
                  (by rw [shape, List.append_assoc]) (step value) accepted
                rw [replay_append, replayed, Option.bind_some, ← shape]
                exact replay_receive absorb table absorbed history message recovered
      · simp only [Step, absorbed] at step
        rw [transform_send absorb _ absorbed] at accepted
        rw [transform_send absorb _ absorbed]
        apply ih value (events ++ [event]) _ proof _ (by rw [shape, List.append_assoc]) step
          accepted
        rw [replay_append, replayed, Option.bind_some, ← shape]
        exact replay_send absorb table absorbed history
      · rw [transform_query absorb _ absorbed] at accepted
        rw [transform_query absorb _ absorbed, answer, tableQueryLog_query_bind]
        by_cases stays : certificate.doomed (next (decode (table (history ++ [event]))))
        · obtain ⟨query, logged, bad⟩ := ih (decode (table (history ++ [event])))
            (events ++ [event]) _ proof
            (by
              rw [replay_append, replayed, Option.bind_some, ← shape]
              exact replay_query absorb table absorbed history)
            (by rw [shape, List.append_assoc]) stays accepted
          exact ⟨query, List.mem_cons_of_mem _ logged, bad⟩
        · refine ⟨⟨history ++ [event], table (history ++ [event])⟩, List.mem_cons_self, ?_⟩
          refine ⟨statement, events, event, .call operation next, by rw [shape], replayed, ?_⟩
          simp only [Escapes, absorbed, true_and]
          exact ⟨doomed, stays⟩
      · rw [transform_refuse absorb _ absorbed] at accepted
        exact accepted.elim

end Bad

/-- The prover chooses a statement and a proof; the transform runs that
statement's validator from that statement's initial history. -/
def experiment (absorb : Interface I E P B) (validator : Stmt → PIR.Proc I A)
    (initial : Stmt → List E) (prover : OracleComp (List E →ₒ B) (Stmt × List P)) :
    OracleComp (List E →ₒ B) (Stmt × (PIR.Outcome A × List P)) :=
  prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
    transform absorb answer (validator claimed.1) (initial claimed.1) claimed.2

/-- The prover's oracle computation followed by the transform of `validator`
from the history `initial`, sharing one oracle. -/
def fixedExperiment (absorb : Interface I E P B) (validator : PIR.Proc I A) (initial : List E)
    (prover : OracleComp (List E →ₒ B) (List P)) :
    OracleComp (List E →ₒ B) (PIR.Outcome A × List P) :=
  prover >>= fun proof => transform absorb answer validator initial proof

section Theorems
variable [DecidableEq E] [SampleableType B]

/-- Fiat–Shamir soundness with adaptively chosen statements and an error per
query site.

The prover is any oracle computation on the transcript oracle; it may hold
arbitrary internal state, query any history and choose the statement after its
queries. Charging every oracle key the error of its last event, its queries
charge at most `proverCost` on every path (repeats and cache hits included). The
initial history determines the statement. The oracle starts with an empty cache
and is shared with the transform, whose queries charge at most `validatorCost`.
A statement satisfying `falseStatement` has a doomed validator. -/
theorem adaptive_soundness_weighted {absorb : Interface I E P B} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement, CostBound absorb error (validator statement) validatorCost)
    (prover : OracleComp (List E →ₒ B) (Stmt × List P)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ proverCost + validatorCost :=
  prEvent_randomOracle_le_of_bad_queries_weighted
    (experiment absorb validator initial prover) (keyError error) (proverCost + validatorCost)
    (WorstCaseCostBound.bind proverBound fun claimed => worstCaseCostBound_map _ _ _ _
      (transform_costBound absorb error (validator claimed.1) validatorCost (initial claimed.1)
        claimed.2 (validatorBound claimed.1)))
    (fun result => falseStatement result.1 ∧ Accepted accepts result.2.1)
    (BadKey absorb certificate.doomed validator initial)
    (badKey_resample certificate validator initial determined) (by
      intro table accepted
      simp only [experiment, evalWithAnswerFn_bind, evalWithAnswerFn_map,
        evalWithAnswerFn_transform] at accepted
      obtain ⟨query, logged, bad⟩ := escape_logged certificate validator initial table
        (evalWithAnswerFn (QueryImpl.ofFn table) prover).1
        (validator (evalWithAnswerFn (QueryImpl.ofFn table) prover).1) []
        (initial (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
        (evalWithAnswerFn (QueryImpl.ofFn table) prover).2 (by simp) (by simp)
        (doomedValidator _ accepted.1) accepted.2
      refine ⟨query, ?_, bad⟩
      rw [experiment, tableQueryLog_bind, tableQueryLog_map]
      exact List.mem_append_right _ logged)

/-- Fiat–Shamir soundness with adaptively chosen statements, for a prover with
at most `queries` oracle queries and validators with at most `budget` queries
on every path, when every site's error is at most `bound`. -/
theorem adaptive_soundness {absorb : Interface I E P B} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, QueryBound absorb (validator statement) budget)
    (prover : OracleComp (List E →ₒ B) (Stmt × List P)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ (queries + budget) * bound := by
  have keyBounded : ∀ key, keyError error key ≤ bound := by
    intro key
    unfold keyError
    split
    · exact bounded _
    · exact zero_le
  have total := adaptive_soundness_weighted certificate validator initial determined
    falseStatement doomedValidator (budget * bound)
    (fun statement => QueryBound.costBound absorb error bounded _ budget
      (validatorBound statement))
    prover (queries * bound)
    (worstCaseCostBound_of_isTotalQueryBound _ keyBounded prover queries proverBound)
  rwa [← add_mul] at total

/-- Fiat–Shamir soundness for a fixed statement, with an error per query site.
The prover's queries charge at most `proverCost` on every path and the
validator's at most `validatorCost`. -/
theorem soundness_weighted {absorb : Interface I E P B} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : PIR.Proc I A) (doomedValidator : certificate.doomed validator)
    (validatorCost : ENNReal) (validatorBound : CostBound absorb error validator validatorCost)
    (initial : List E) (prover : OracleComp (List E →ₒ B) (List P)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run'
        ∅}[Accepted accepts result.1] ≤ proverCost + validatorCost :=
  prEvent_randomOracle_le_of_bad_queries_weighted
    (fixedExperiment absorb validator initial prover) (keyError error)
    (proverCost + validatorCost)
    (WorstCaseCostBound.bind proverBound fun proof =>
      transform_costBound absorb error validator validatorCost initial proof validatorBound)
    (fun result => Accepted accepts result.1)
    (BadKey absorb certificate.doomed (fun _ : Unit => validator) (fun _ => initial))
    (badKey_resample certificate _ _ (fun _ _ _ _ _ => rfl)) (by
      intro table accepted
      simp only [fixedExperiment, evalWithAnswerFn_bind, evalWithAnswerFn_transform] at accepted
      obtain ⟨query, logged, bad⟩ := escape_logged certificate (fun _ : Unit => validator)
        (fun _ => initial) table () validator [] initial
        (evalWithAnswerFn (QueryImpl.ofFn table) prover) (by simp) (by simp) doomedValidator
        accepted
      refine ⟨query, ?_, bad⟩
      rw [fixedExperiment, tableQueryLog_bind]
      exact List.mem_append_right _ logged)

/-- Fiat–Shamir soundness for a fixed statement: a prover with at most `queries`
oracle queries makes the transform of a doomed validator with at most `budget`
queries accept with probability at most `(queries + budget) * bound` when every
site's error is at most `bound`. -/
theorem soundness {absorb : Interface I E P B} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound)
    (validator : PIR.Proc I A) (doomedValidator : certificate.doomed validator)
    (budget : ℕ) (validatorBound : QueryBound absorb validator budget) (initial : List E)
    (prover : OracleComp (List E →ₒ B) (List P)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run'
        ∅}[Accepted accepts result.1] ≤ (queries + budget) * bound := by
  have keyBounded : ∀ key, keyError error key ≤ bound := by
    intro key
    unfold keyError
    split
    · exact bounded _
    · exact zero_le
  have total := soundness_weighted certificate validator doomedValidator (budget * bound)
    (QueryBound.costBound absorb error bounded validator budget validatorBound) initial prover
    (queries * bound)
    (worstCaseCostBound_of_isTotalQueryBound _ keyBounded prover queries proverBound)
  rwa [← add_mul] at total

/-- Private randomness sampled before the oracle computation: every prover in
the support of `provers` is bounded by `proverCost`, so the mixture inherits the
bound. -/
theorem randomized_soundness_weighted {absorb : Interface I E P B} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : PIR.Proc I A) (doomedValidator : certificate.doomed validator)
    (validatorCost : ENNReal) (validatorBound : CostBound absorb error validator validatorCost)
    (initial : List E) (provers : ProbComp (OracleComp (List E →ₒ B) (List P)))
    (proverCost : ENNReal)
    (proverBound : ∀ prover ∈ support provers,
      WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ proverCost + validatorCost :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    soundness_weighted certificate validator doomedValidator validatorCost validatorBound initial
      prover proverCost (proverBound prover drawn)

end Theorems

end ZkcSecurity.FiatShamir.Typed
