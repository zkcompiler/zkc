module

public import ZkcSecurity.FiatShamir.Replay
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

@[expose] public section

/-! Fiat–Shamir soundness of `Zkc.Construction.transform` from round-by-round
soundness of the transformed validator.

The ideal experiment: a prover makes arbitrary adaptive queries to a lazily
sampled random oracle on all typed transcript histories, starting from an
empty cache, and outputs a proof; the transform of the validator then answers
each of its challenges with the same oracle at the absorbed history ending in
the challenge occurrence. Every query of the whole execution counts, including
repeated and cached ones.

Round-by-round soundness (`RoundByRound`) is a set of doomed validator residuals
closed under received and sent messages, containing no accepting result, and
left by a fresh uniform challenge with probability at most `error`. If the
validator starts doomed and makes at most `budget` challenges on every path,
then a prover with at most `queries` oracle queries makes the transform accept
with probability at most `(queries + budget) * error` (`soundness`).

The proof applies VCVio's adaptive bad-query bound
(`OracleComp.prEvent_randomOracle_le_of_bad_queries`) directly to the history
oracle. A key is bad when replaying the validator along the key reaches a
doomed challenge whose answer at the key leaves the doomed set. Replay reads
the oracle only at shorter histories, so resampling the key's answer leaves the
replayed residual unchanged; an accepting run from a doomed validator must leave
the doomed set at one of its own challenges, which are in the query log.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Construction Zkc.Source.Common.Native

variable {F G A : Type}

/-- The transcript oracle on all typed histories. -/
abbrev Spec (F G : Type) := History F G →ₒ F

/-- One transcript challenge: a query of the oracle at the absorbed history. -/
def historyQuery (history : History F G) : OracleComp (Spec F G) F :=
  liftM ((Spec F G).query history)

/-- A returned value satisfying the acceptance predicate. Stops never accept. -/
def Accepted (accepts : A → Prop) : PIR.Outcome A → Prop
  | .returned value => accepts value
  | .stopped _ => False

/-- At most `budget` challenge queries on every path, for every reply. -/
def QueryBound : PIR.Proc (Actions F G) A → ℕ → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call (.receive _ _ _) next, budget => ∀ value, QueryBound (next value) budget
  | .call (.send _ _ _) next, budget => QueryBound (next ()) budget
  | .call (.query _ _ _) next, budget =>
      0 < budget ∧ ∀ challenge, QueryBound (next challenge) (budget - 1)

/-- The prover's oracle computation followed by the transform of `validator`
from the history `initial`, sharing one oracle. -/
def experiment (context : Context) (validator : PIR.Proc (Actions F G) A)
    (initial : History F G) (prover : OracleComp (Spec F G) (Proof F G)) :
    OracleComp (Spec F G) (PIR.Outcome A × Proof F G) :=
  prover >>= fun proof => transform context historyQuery validator initial proof

section RoundByRound
variable [SampleableType F]

/-- Round-by-round soundness of validators over the common participant actions:
a doomed set of residual processes that received or sent messages cannot leave,
that contains no accepting result, and that a fresh uniform challenge leaves
with probability at most `error`. -/
structure RoundByRound (accepts : A → Prop) (error : ENNReal) where
  doomed : PIR.Proc (Actions F G) A → Prop
  done : ∀ value, doomed (.done value) → ¬ accepts value
  receive : ∀ (ty : Ty) (site : String) (sender : Nat)
    (next : ScalarValue F G ty → PIR.Proc (Actions F G) A),
    doomed (.call (.receive ty site sender) next) → ∀ value, doomed (next value)
  send : ∀ (ty : Ty) (site : String) (receiver : Nat) (sent : ScalarValue F G ty)
    (next : Unit → PIR.Proc (Actions F G) A),
    doomed (.call (.send site receiver sent) next) → doomed (next ())
  query : ∀ (site : String) (op : services.Op)
    (arguments : Values (ScalarValue F G) (services.arguments op))
    (next : F → PIR.Proc (Actions F G) A),
    doomed (.call (.query site op arguments) next) →
      Pr{let challenge ← $ᵗ F}[¬ doomed (next challenge)] ≤ error

/-- The local obligation of a doomed set at one residual. -/
def Step (doomed : PIR.Proc (Actions F G) A → Prop) (accepts : A → Prop) (error : ENNReal) :
    PIR.Proc (Actions F G) A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call (.receive _ _ _) next => ∀ value, doomed (next value)
  | .call (.send _ _ _) next => doomed (next ())
  | .call (.query _ _ _) next => Pr{let challenge ← $ᵗ F}[¬ doomed (next challenge)] ≤ error

/-- A doomed set whose every member meets its local obligation. -/
def RoundByRound.ofStep {accepts : A → Prop} {error : ENNReal}
    (doomed : PIR.Proc (Actions F G) A → Prop)
    (step : ∀ process, doomed process → Step doomed accepts error process) :
    RoundByRound (F := F) (G := G) accepts error where
  doomed := doomed
  done _ member := step _ member
  receive _ _ _ _ member := step _ member
  send _ _ _ _ _ member := step _ member
  query _ _ _ _ member := step _ member

end RoundByRound

section Execution

/-- Deterministic evaluation of the oracle transform against a total table is
the transform with that table as challenge function. -/
theorem evalWithAnswerFn_transform (context : Context) (table : History F G → F) :
    ∀ (process : PIR.Proc (Actions F G) A) (history : History F G) (proof : Proof F G),
      evalWithAnswerFn (QueryImpl.ofFn table)
          (transform context historyQuery process history proof) =
        transform (m := Id) context table process history proof := by
  intro process
  induction process with
  | done value => intro history proof; rfl
  | halt stop => intro history proof; rfl
  | call operation next ih =>
      intro history proof
      cases operation with
      | receive ty site sender =>
          cases proof with
          | nil => rfl
          | cons payload rest =>
              simp only [transform]
              cases payload.value ty with
              | none => rfl
              | some value => exact ih value _ _
      | query site op arguments =>
          simp only [transform, historyQuery, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
            QueryImpl.ofFn_apply]
          exact ih _ _ _
      | send site receiver sent =>
          simp only [transform]
          cases Payload.ofValue _ sent with
          | none => rfl
          | some payload => exact ih () _ _

/-- The transform makes at most the validator's challenge budget of queries. -/
theorem transform_queryBound (context : Context) :
    ∀ (process : PIR.Proc (Actions F G) A) (budget : ℕ) (history : History F G)
      (proof : Proof F G), QueryBound process budget →
      IsTotalQueryBound (transform context historyQuery process history proof) budget := by
  intro process
  induction process with
  | done value => intro budget history proof _; trivial
  | halt stop => intro budget history proof _; trivial
  | call operation next ih =>
      intro budget history proof bounded
      cases operation with
      | receive ty site sender =>
          cases proof with
          | nil => trivial
          | cons payload rest =>
              simp only [transform]
              cases payload.value ty with
              | none => trivial
              | some value => exact ih value budget _ _ (bounded value)
      | query site op arguments =>
          simp only [transform, historyQuery]
          exact isTotalQueryBound_query_bind_iff.mpr
            ⟨bounded.1, fun challenge => ih challenge _ _ _ (bounded.2 challenge)⟩
      | send site receiver sent =>
          simp only [transform]
          cases Payload.ofValue _ sent with
          | none => trivial
          | some payload => exact ih () budget _ _ bounded

end Execution

section Bad
variable [DecidableEq F] [DecidableEq G]

/-- The answer `challenge` to a doomed challenge occurrence leaves the doomed
set. Only challenge nodes can escape. -/
def Escapes (doomed : PIR.Proc (Actions F G) A → Prop) (context : Context) :
    PIR.Proc (Actions F G) A → Event F G → F → Prop
  | .call (.query site op arguments) next, event, challenge =>
      event = .challenge (context.query site) ∧
        doomed (.call (.query site op arguments) next) ∧ ¬ doomed (next challenge)
  | _, _, _ => False

/-- A bad oracle key: replaying the validator from `initial` along the key's
events before its last one reaches a residual whose challenge, answered by the
table at the key, escapes the doomed set. -/
def BadKey (doomed : PIR.Proc (Actions F G) A → Prop) (context : Context)
    (validator : PIR.Proc (Actions F G) A) (initial key : History F G)
    (table : History F G → F) : Prop :=
  ∃ events event process, key = initial ++ events ++ [event] ∧
    replay context table validator initial events = some process ∧
    Escapes doomed context process event (table key)

theorem update_agrees (table : History F G → F) (initial events : History F G)
    (event : Event F G) (answer : F) :
    ∀ other : History F G, other.length ≤ initial.length + events.length →
      Function.update table (initial ++ events ++ [event]) answer other = table other := by
  intro other bound
  apply Function.update_of_ne
  intro same
  rw [same] at bound
  simp at bound

omit [DecidableEq F] [DecidableEq G] in
/-- Two decompositions of one key agree. -/
theorem key_shape {initial events events' : History F G} {event event' : Event F G}
    (same : initial ++ events ++ [event] = initial ++ events' ++ [event']) :
    events = events' ∧ event = event' := by
  rw [List.append_assoc, List.append_assoc] at same
  obtain ⟨prefixes, lasts⟩ := List.append_inj' (List.append_cancel_left same) rfl
  exact ⟨prefixes, List.singleton_inj.mp lasts⟩

/-- The replayed residual before a key does not depend on the answer at the key. -/
theorem replay_update (context : Context) (table : History F G → F)
    (validator : PIR.Proc (Actions F G) A) (initial events : History F G)
    (event : Event F G) (answer : F) :
    replay context (Function.update table (initial ++ events ++ [event]) answer) validator
        initial events =
      replay context table validator initial events :=
  (replay_congr context table events validator initial
    (fun other bound => (update_agrees table initial events event answer other bound).symm)).symm

variable [SampleableType F]

omit [DecidableEq F] [DecidableEq G] in
/-- A fixed residual escapes at a fresh uniform answer with probability at most
`error`. -/
theorem escapes_le {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (process : PIR.Proc (Actions F G) A) (event : Event F G) :
    Pr{let answer ← $ᵗ F}[Escapes certificate.doomed context process event answer] ≤ error := by
  have impossible : (∀ answer, ¬ Escapes certificate.doomed context process event answer) →
      Pr{let answer ← $ᵗ F}[Escapes certificate.doomed context process event answer] ≤ error :=
    fun never => (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le
  cases process with
  | done value => exact impossible fun _ escapes => escapes
  | halt stop => exact impossible fun _ escapes => escapes
  | call operation next =>
      cases operation with
      | receive ty site sender => exact impossible fun _ escapes => escapes
      | send site receiver sent => exact impossible fun _ escapes => escapes
      | query site op arguments =>
          by_cases doomed : certificate.doomed (.call (.query site op arguments) next)
          · exact (prEvent_mono _ _ (fun answer => ¬ certificate.doomed (next answer))
              (fun _ escapes => escapes.2.2)).trans
              (certificate.query site op arguments next doomed)
          · exact impossible fun _ escapes => doomed escapes.2.1

/-- Resampling the answer at any key, under every background table, makes the
key bad with probability at most `error`. -/
theorem badKey_resample {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (validator : PIR.Proc (Actions F G) A) (initial key : History F G)
    (table : History F G → F) :
    Pr{let answer ← $ᵗ F}[
      BadKey certificate.doomed context validator initial key (Function.update table key answer)] ≤
      error := by
  by_cases found : ∃ events event process, key = initial ++ events ++ [event] ∧
      replay context table validator initial events = some process
  · obtain ⟨events, event, process, shape, replayed⟩ := found
    subst shape
    have reduced : ∀ answer,
        BadKey certificate.doomed context validator initial (initial ++ events ++ [event])
            (Function.update table (initial ++ events ++ [event]) answer) →
          Escapes certificate.doomed context process event answer := by
      rintro answer ⟨events', event', process', shape', replayed', escapes⟩
      obtain ⟨rfl, rfl⟩ := key_shape shape'
      rw [replay_update, replayed] at replayed'
      cases replayed'
      simpa using escapes
    exact (prEvent_mono _ _ _ reduced).trans (escapes_le certificate context process event)
  · have never : ∀ answer, ¬ BadKey certificate.doomed context validator initial key
        (Function.update table key answer) := by
      rintro answer ⟨events, event, process, shape, replayed, _⟩
      subst shape
      rw [replay_update] at replayed
      exact found ⟨events, event, process, rfl, replayed⟩
    exact (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le

/-- An accepting run of the transform, against a total challenge table, from a
doomed residual reached by replay queries a bad key. -/
theorem escape_logged {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (validator : PIR.Proc (Actions F G) A) (initial : History F G) (table : History F G → F) :
    ∀ (process : PIR.Proc (Actions F G) A) (events history : History F G) (proof : Proof F G),
      replay context table validator initial events = some process →
      history = initial ++ events →
      certificate.doomed process →
      Accepted accepts (transform (m := Id) context table process history proof).1 →
      ∃ query ∈ tableQueryLog (transform context historyQuery process history proof) table,
        BadKey certificate.doomed context validator initial query.1 table := by
  intro process
  induction process with
  | done value =>
      intro events history proof _ _ doomed accepted
      exact absurd accepted (certificate.done value doomed)
  | halt stop =>
      intro events history proof _ _ _ accepted
      exact accepted.elim
  | call operation next ih =>
      intro events history proof replayed shape doomed accepted
      cases operation with
      | receive ty site sender =>
          cases proof with
          | nil => exact accepted.elim
          | cons payload rest =>
              simp only [transform] at accepted ⊢
              cases decoded : payload.value ty with
              | none =>
                  rw [decoded] at accepted
                  exact accepted.elim
              | some value =>
                  rw [decoded] at accepted
                  simp only
                  apply ih value
                    (events ++ [.message (context.message site sender context.validator) payload])
                    _ rest _ (by rw [shape, List.append_assoc])
                    (certificate.receive ty site sender next doomed value) accepted
                  rw [replay_append, replayed, Option.bind_some, ← shape]
                  exact replay_receive context table ty site sender next history payload value
                    decoded
      | query site op arguments =>
          simp only [transform, historyQuery] at accepted ⊢
          rw [tableQueryLog_query_bind]
          by_cases stays : certificate.doomed
              (next (table (history ++ [.challenge (context.query site)])))
          · obtain ⟨query, logged, bad⟩ := ih (table (history ++ [.challenge (context.query site)]))
              (events ++ [.challenge (context.query site)]) _ proof
              (by
                rw [replay_append, replayed, Option.bind_some, ← shape]
                exact replay_query context table site op arguments next history)
              (by rw [shape, List.append_assoc]) stays accepted
            exact ⟨query, List.mem_cons_of_mem _ logged, bad⟩
          · refine ⟨⟨history ++ [.challenge (context.query site)],
              table (history ++ [.challenge (context.query site)])⟩, List.mem_cons_self, ?_⟩
            exact ⟨events, .challenge (context.query site), .call (.query site op arguments) next,
              by rw [shape], replayed, rfl, doomed, stays⟩
      | send site receiver sent =>
          simp only [transform] at accepted ⊢
          cases encoded : Payload.ofValue _ sent with
          | none =>
              rw [encoded] at accepted
              exact accepted.elim
          | some payload =>
              rw [encoded] at accepted
              simp only
              apply ih ()
                (events ++ [.message (context.message site context.validator receiver) payload])
                _ proof _ (by rw [shape, List.append_assoc])
                (certificate.send _ site receiver sent next doomed) accepted
              rw [replay_append, replayed, Option.bind_some, ← shape]
              exact replay_send context table site receiver sent next history payload encoded

/-- Fiat–Shamir soundness of the transform from round-by-round soundness.

The prover is any oracle computation on the history oracle making at most
`queries` queries on every path (repeats and cache hits included); it may hold
arbitrary internal state and query any typed history. The statement is fixed:
`validator` and `initial` are chosen before the experiment. The oracle starts
with an empty cache and is shared by the prover and the transform. The
transform's own challenges add at most `budget` queries. -/
theorem soundness {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (validator : PIR.Proc (Actions F G) A) (doomedValidator : certificate.doomed validator)
    (budget : ℕ) (validatorBound : QueryBound validator budget) (initial : History F G)
    (prover : OracleComp (Spec F G) (Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (experiment context validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + budget) * error := by
  have bound := prEvent_randomOracle_le_of_bad_queries (experiment context validator initial prover)
    (queries + budget)
    (isTotalQueryBound_bind proverBound fun proof =>
      transform_queryBound context validator budget initial proof validatorBound)
    (fun result => Accepted accepts result.1) (BadKey certificate.doomed context validator initial)
    error (badKey_resample certificate context validator initial) (by
      intro table accepted
      simp only [experiment, evalWithAnswerFn_bind, evalWithAnswerFn_transform] at accepted
      obtain ⟨query, logged, bad⟩ := escape_logged certificate context validator initial table
        validator [] initial (evalWithAnswerFn (QueryImpl.ofFn table) prover) (by simp)
        (by simp) doomedValidator accepted
      refine ⟨query, ?_, bad⟩
      rw [experiment, tableQueryLog_bind]
      exact List.mem_append_right _ logged)
  simpa only [Nat.cast_add] using bound

/-- Private randomness sampled before the oracle computation: every prover in
the support of `provers` is bounded by `queries`, so the mixture inherits the
bound. -/
theorem randomized_soundness {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (validator : PIR.Proc (Actions F G) A) (doomedValidator : certificate.doomed validator)
    (budget : ℕ) (validatorBound : QueryBound validator budget) (initial : History F G)
    (provers : ProbComp (OracleComp (Spec F G) (Proof F G))) (queries : ℕ)
    (proverBound : ∀ prover ∈ support provers, IsTotalQueryBound prover queries) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (experiment context validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + budget) * error :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    soundness certificate context validator doomedValidator budget validatorBound initial prover
      queries (proverBound prover drawn)

end Bad

end ZkcSecurity.FiatShamir
