module

public import ZkcSecurity.FiatShamir.Replay
public import Zkc.Construction.Soundness
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

Two generalizations share the same proof. The oracle may answer in another
type `B`, decoded to a field challenge by `decode`; a decoding whose events
exceed the uniform field's by at most `loss` adds `loss` per query
(`Balanced`). The prover may also choose the statement after its queries,
when the initial history determines the statement (`Determined`); the
transform then runs the statement's validator from the statement's initial
history (`adaptive_soundness`). Private randomness drawn before the oracle
computation is a distribution over provers (`randomized_soundness`).

Compiled verifiers reach these bounds through their relation to the transform.
One that is an outcome image of the transform, accepting only where the
transform accepts, accepts no more often (`acceptance_le_of_image`, fixed
statement). A final projection of the validator's result moves into the
acceptance predicate, for fixed and adaptive statements (`acceptance_bind_done`,
`adaptive_acceptance_bind_done`).

The proof applies VCVio's adaptive bad-query bound
(`OracleComp.prEvent_randomOracle_le_of_bad_queries`) directly to the history
oracle. A key is bad when replaying a statement's validator along the key
reaches a doomed challenge whose answer at the key leaves the doomed set.
Replay reads the oracle only at shorter histories and the key determines the
statement, so resampling the key's answer leaves the replayed residual
unchanged; an accepting run from a doomed validator must leave the doomed set
at one of its own challenges, which are in the query log.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Construction Zkc.Source.Common.Native

variable {F G A B Stmt : Type}

/-- The transcript oracle on all typed histories, answering in `B`. -/
abbrev Oracle (F G B : Type) := History F G →ₒ B

/-- The transcript oracle answering field challenges directly. -/
abbrev FieldOracle (F G : Type) := Oracle F G F

/-- One transcript challenge: a query of the oracle at the absorbed history. -/
def historyQuery (history : History F G) : OracleComp (FieldOracle F G) F :=
  liftM ((FieldOracle F G).query history)

/-- One transcript challenge decoded from the oracle's answer. -/
def decodedQuery (decode : B → F) (history : History F G) : OracleComp (Oracle F G B) F :=
  decode <$> liftM ((Oracle F G B).query history)

theorem decodedQuery_id : decodedQuery (F := F) (G := G) (id : F → F) = historyQuery := by
  funext history
  exact id_map _

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

theorem QueryBound.mono :
    ∀ (process : PIR.Proc (Actions F G) A) {budget larger : ℕ},
      QueryBound process budget → budget ≤ larger → QueryBound process larger
  | .done _, _, _, _, _ => trivial
  | .halt _, _, _, _, _ => trivial
  | .call (.receive _ _ _) next, _, _, bounded, le => fun value =>
      QueryBound.mono (next value) (bounded value) le
  | .call (.send _ _ _) next, _, _, bounded, le => QueryBound.mono (next ()) bounded le
  | .call (.query _ _ _) next, _, _, bounded, le =>
      ⟨Nat.lt_of_lt_of_le bounded.1 le, fun challenge =>
        QueryBound.mono (next challenge) (bounded.2 challenge) (Nat.sub_le_sub_right le 1)⟩

/-- The prover's oracle computation followed by the transform of `validator`
from the history `initial`, sharing one oracle. -/
def experiment (context : Context) (validator : PIR.Proc (Actions F G) A)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) :
    OracleComp (FieldOracle F G) (PIR.Outcome A × Proof F G) :=
  prover >>= fun proof => transform context historyQuery validator initial proof

/-- The prover chooses a statement and a proof; the transform runs that
statement's validator from that statement's initial history. -/
def adaptiveExperiment (context : Context) (decode : B → F)
    (validator : Stmt → PIR.Proc (Actions F G) A) (initial : Stmt → History F G)
    (prover : OracleComp (Oracle F G B) (Stmt × Proof F G)) :
    OracleComp (Oracle F G B) (Stmt × (PIR.Outcome A × Proof F G)) :=
  prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
    transform context (decodedQuery decode) (validator claimed.1) (initial claimed.1) claimed.2

/-- The initial histories determine the statements: when two statements' initial
histories, each followed by some events, are equal, the statements are equal.
Injective initial histories of which none is a proper prefix of another satisfy
this. -/
def Determined (initial : Stmt → History F G) : Prop :=
  ∀ statement other (rest otherRest : History F G),
    initial statement ++ rest = initial other ++ otherRest → statement = other

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

/-- Enlarging the doomed set keeps every local obligation. -/
theorem Step.mono {accepts : A → Prop} {error : ENNReal}
    {small large : PIR.Proc (Actions F G) A → Prop}
    (included : ∀ process, small process → large process) :
    ∀ process, Step small accepts error process → Step large accepts error process
  | .done _, step => step
  | .halt _, step => step
  | .call (.receive _ _ _) _, step => fun value => included _ (step value)
  | .call (.send _ _ _) _, step => included _ step
  | .call (.query _ _ _) next, step =>
      (prEvent_mono _ _ (fun challenge => ¬ small (next challenge))
        (fun _ outside inside => outside (included _ inside))).trans step

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

/-- Decoded oracle answers: every event of the decoded challenge is at most
`loss` likelier than under the uniform field. -/
def Balanced [SampleableType B] (decode : B → F) (loss : ENNReal) : Prop :=
  ∀ event : F → Prop,
    Pr{let answer ← $ᵗ B}[event (decode answer)] ≤ Pr{let challenge ← $ᵗ F}[event challenge] + loss

theorem balanced_id : Balanced (B := F) (id : F → F) 0 := fun _ => by simp

end RoundByRound

section Execution

theorem map_queryBound {α β : Type} (f : α → β) (computation : OracleComp (Oracle F G B) α)
    (budget : ℕ) (bounded : IsTotalQueryBound computation budget) :
    IsTotalQueryBound (f <$> computation) budget := by
  have composed := isTotalQueryBound_bind (n₂ := 0) bounded
    (ob := fun value => (pure (f value) : OracleComp (Oracle F G B) β)) fun _ => trivial
  rw [Nat.add_zero] at composed
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using composed

theorem tableQueryLog_map {α β : Type} (f : α → β) (computation : OracleComp (Oracle F G B) α)
    (table : History F G → B) :
    tableQueryLog (f <$> computation) table = tableQueryLog computation table := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind]
  simp

/-- Deterministic evaluation of the oracle transform against a total table is
the transform with the decoded table as challenge function. -/
theorem evalWithAnswerFn_transform (context : Context) (decode : B → F)
    (table : History F G → B) :
    ∀ (process : PIR.Proc (Actions F G) A) (history : History F G) (proof : Proof F G),
      evalWithAnswerFn (QueryImpl.ofFn table)
          (transform context (decodedQuery decode) process history proof) =
        transform (m := Id) context (fun key => decode (table key)) process history proof := by
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
          simp only [transform, decodedQuery, bind_map_left, evalWithAnswerFn_bind,
            evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
          exact ih _ _ _
      | send site receiver sent =>
          simp only [transform]
          cases Payload.ofValue _ sent with
          | none => rfl
          | some payload => exact ih () _ _

/-- The transform makes at most the validator's challenge budget of queries. -/
theorem transform_queryBound (context : Context) (decode : B → F) :
    ∀ (process : PIR.Proc (Actions F G) A) (budget : ℕ) (history : History F G)
      (proof : Proof F G), QueryBound process budget →
      IsTotalQueryBound (transform context (decodedQuery decode) process history proof) budget := by
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
          simp only [transform, decodedQuery, bind_map_left]
          exact isTotalQueryBound_query_bind_iff.mpr
            ⟨bounded.1, fun answer => ih _ _ _ _ (bounded.2 _)⟩
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

/-- A bad oracle key: for some statement, replaying its validator from its
initial history along the key's events before the last one reaches a residual
whose challenge, answered by the decoded table at the key, escapes the doomed
set. -/
def BadKey (doomed : PIR.Proc (Actions F G) A → Prop) (context : Context) (decode : B → F)
    (validator : Stmt → PIR.Proc (Actions F G) A) (initial : Stmt → History F G)
    (key : History F G) (table : History F G → B) : Prop :=
  ∃ statement events event process, key = initial statement ++ events ++ [event] ∧
    replay context (fun history => decode (table history)) (validator statement)
      (initial statement) events = some process ∧
    Escapes doomed context process event (decode (table key))

theorem update_agrees (table : History F G → B) (initial events : History F G)
    (event : Event F G) (answer : B) :
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
theorem replay_update (context : Context) (decode : B → F) (table : History F G → B)
    (validator : PIR.Proc (Actions F G) A) (initial events : History F G)
    (event : Event F G) (answer : B) :
    replay context (fun history => decode (Function.update table (initial ++ events ++ [event])
        answer history)) validator initial events =
      replay context (fun history => decode (table history)) validator initial events :=
  replay_congr context _ events validator initial
    (fun other bound =>
      congrArg decode (update_agrees table initial events event answer other bound))

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

variable [SampleableType B]

/-- Resampling the answer at any key, under every background table, makes the
key bad with probability at most `error + loss`. -/
theorem badKey_resample {accepts : A → Prop} {error loss : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (balanced : Balanced decode loss)
    (validator : Stmt → PIR.Proc (Actions F G) A) (initial : Stmt → History F G)
    (determined : Determined initial) (key : History F G) (table : History F G → B) :
    Pr{let answer ← $ᵗ B}[BadKey certificate.doomed context decode validator initial key
      (Function.update table key answer)] ≤ error + loss := by
  by_cases found : ∃ statement events event process,
      key = initial statement ++ events ++ [event] ∧
      replay context (fun history => decode (table history)) (validator statement)
        (initial statement) events = some process
  · obtain ⟨statement, events, event, process, shape, replayed⟩ := found
    subst shape
    have reduced : ∀ answer,
        BadKey certificate.doomed context decode validator initial
            (initial statement ++ events ++ [event])
            (Function.update table (initial statement ++ events ++ [event]) answer) →
          Escapes certificate.doomed context process event (decode answer) := by
      rintro answer ⟨statement', events', event', process', shape', replayed', escapes⟩
      have same : statement = statement' := determined _ _ (events ++ [event])
        (events' ++ [event']) (by simpa only [List.append_assoc] using shape')
      subst same
      obtain ⟨rfl, rfl⟩ := key_shape shape'
      rw [replay_update, replayed] at replayed'
      cases replayed'
      simpa using escapes
    calc Pr{let answer ← $ᵗ B}[BadKey certificate.doomed context decode validator initial
            (initial statement ++ events ++ [event])
            (Function.update table (initial statement ++ events ++ [event]) answer)]
        ≤ Pr{let answer ← $ᵗ B}[
            Escapes certificate.doomed context process event (decode answer)] :=
          prEvent_mono _ _ _ reduced
      _ ≤ Pr{let challenge ← $ᵗ F}[Escapes certificate.doomed context process event challenge] +
            loss := balanced _
      _ ≤ error + loss := add_le_add_left (escapes_le certificate context process event) _
  · have never : ∀ answer, ¬ BadKey certificate.doomed context decode validator initial key
        (Function.update table key answer) := by
      rintro answer ⟨statement, events, event, process, shape, replayed, _⟩
      subst shape
      rw [replay_update] at replayed
      exact found ⟨statement, events, event, process, rfl, replayed⟩
    exact (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le

omit [SampleableType B] in
/-- An accepting run of the transform, against a total table, from a doomed
residual reached by replay queries a bad key. -/
theorem escape_logged {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (validator : Stmt → PIR.Proc (Actions F G) A)
    (initial : Stmt → History F G) (table : History F G → B) (statement : Stmt) :
    ∀ (process : PIR.Proc (Actions F G) A) (events history : History F G) (proof : Proof F G),
      replay context (fun key => decode (table key)) (validator statement) (initial statement)
        events = some process →
      history = initial statement ++ events →
      certificate.doomed process →
      Accepted accepts
        (transform (m := Id) context (fun key => decode (table key)) process history proof).1 →
      ∃ query ∈ tableQueryLog (transform context (decodedQuery decode) process history proof) table,
        BadKey certificate.doomed context decode validator initial query.1 table := by
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
                  exact replay_receive context _ ty site sender next history payload value
                    decoded
      | query site op arguments =>
          simp only [transform, decodedQuery, bind_map_left] at accepted ⊢
          rw [tableQueryLog_query_bind]
          by_cases stays : certificate.doomed
              (next (decode (table (history ++ [.challenge (context.query site)]))))
          · obtain ⟨query, logged, bad⟩ := ih
              (decode (table (history ++ [.challenge (context.query site)])))
              (events ++ [.challenge (context.query site)]) _ proof
              (by
                rw [replay_append, replayed, Option.bind_some, ← shape]
                exact replay_query context _ site op arguments next history)
              (by rw [shape, List.append_assoc]) stays accepted
            exact ⟨query, List.mem_cons_of_mem _ logged, bad⟩
          · refine ⟨⟨history ++ [.challenge (context.query site)],
              table (history ++ [.challenge (context.query site)])⟩, List.mem_cons_self, ?_⟩
            exact ⟨statement, events, .challenge (context.query site),
              .call (.query site op arguments) next, by rw [shape], replayed, rfl, doomed, stays⟩
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
              exact replay_send context _ site receiver sent next history payload encoded

/-- Fiat–Shamir soundness with adaptively chosen statements and decoded
challenges.

The prover is any oracle computation on the transcript oracle answering in `B`,
making at most `queries` queries on every path (repeats and cache hits
included); it may hold arbitrary internal state, query any typed history, and
choose the statement after its queries. The initial history determines the
statement. The oracle starts with an empty cache and is shared with the
transform, whose challenges add at most `budget` queries. A statement satisfying
`falseStatement` has a doomed validator. -/
theorem adaptive_soundness {accepts : A → Prop} {error loss : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (balanced : Balanced decode loss)
    (validator : Stmt → PIR.Proc (Actions F G) A) (initial : Stmt → History F G)
    (determined : Determined initial) (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, QueryBound (validator statement) budget)
    (prover : OracleComp (Oracle F G B) (Stmt × Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (adaptiveExperiment context decode validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤
      (queries + budget) * (error + loss) := by
  have bound := prEvent_randomOracle_le_of_bad_queries
    (adaptiveExperiment context decode validator initial prover) (queries + budget)
    (isTotalQueryBound_bind proverBound fun claimed => map_queryBound _ _ budget
      (transform_queryBound context decode (validator claimed.1) budget (initial claimed.1)
        claimed.2 (validatorBound claimed.1)))
    (fun result => falseStatement result.1 ∧ Accepted accepts result.2.1)
    (BadKey certificate.doomed context decode validator initial) (error + loss)
    (badKey_resample certificate context decode balanced validator initial determined) (by
      intro table accepted
      simp only [adaptiveExperiment, evalWithAnswerFn_bind, evalWithAnswerFn_map,
        evalWithAnswerFn_transform] at accepted
      obtain ⟨query, logged, bad⟩ := escape_logged certificate context decode validator initial
        table (evalWithAnswerFn (QueryImpl.ofFn table) prover).1
        (validator (evalWithAnswerFn (QueryImpl.ofFn table) prover).1) []
        (initial (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
        (evalWithAnswerFn (QueryImpl.ofFn table) prover).2 (by simp) (by simp)
        (doomedValidator _ accepted.1) accepted.2
      refine ⟨query, ?_, bad⟩
      rw [adaptiveExperiment, tableQueryLog_bind, tableQueryLog_map]
      exact List.mem_append_right _ logged)
  simpa only [Nat.cast_add] using bound

end Bad

section Fixed
variable [DecidableEq F] [DecidableEq G] [SampleableType F]

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
    (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (experiment context validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + budget) * error := by
  have bound := prEvent_randomOracle_le_of_bad_queries (experiment context validator initial prover)
    (queries + budget)
    (isTotalQueryBound_bind proverBound fun proof => by
      rw [← decodedQuery_id]
      exact transform_queryBound context id validator budget initial proof validatorBound)
    (fun result => Accepted accepts result.1)
    (BadKey certificate.doomed context id (fun _ : Unit => validator) (fun _ => initial))
    (error + 0)
    (badKey_resample certificate context id balanced_id _ _ (fun _ _ _ _ _ => rfl)) (by
      intro table accepted
      simp only [experiment, ← decodedQuery_id, evalWithAnswerFn_bind,
        evalWithAnswerFn_transform] at accepted
      obtain ⟨query, logged, bad⟩ := escape_logged certificate context id
        (fun _ : Unit => validator) (fun _ => initial) table () validator [] initial
        (evalWithAnswerFn (QueryImpl.ofFn table) prover) (by simp) (by simp) doomedValidator
        accepted
      refine ⟨query, ?_, bad⟩
      rw [experiment, ← decodedQuery_id, tableQueryLog_bind]
      exact List.mem_append_right _ logged)
  simpa only [Nat.cast_add, add_zero] using bound

/-- Private randomness sampled before the oracle computation: every prover in
the support of `provers` is bounded by `queries`, so the mixture inherits the
bound. -/
theorem randomized_soundness {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (validator : PIR.Proc (Actions F G) A) (doomedValidator : certificate.doomed validator)
    (budget : ℕ) (validatorBound : QueryBound validator budget) (initial : History F G)
    (provers : ProbComp (OracleComp (FieldOracle F G) (Proof F G))) (queries : ℕ)
    (proverBound : ∀ prover ∈ support provers, IsTotalQueryBound prover queries) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (experiment context validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + budget) * error :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    soundness certificate context validator doomedValidator budget validatorBound initial prover
      queries (proverBound prover drawn)

/-- Transfer to a compiled verifier for a fixed statement. If, for every proof,
the compiled verifier is an outcome image of the transform of `validator`, and an
accepted image comes only from an accepted outcome, the compiled verifier accepts
no more often than the transform. The image covers an acceptance projection and
stop reasons that the compiled program reports differently. -/
theorem acceptance_le_of_image {A' : Type} (context : Context)
    (validator : PIR.Proc (Actions F G) A) (initial : History F G)
    (compiled : Proof F G → OracleComp (FieldOracle F G) (PIR.Outcome A' × Proof F G))
    (image : PIR.Outcome A × Proof F G → PIR.Outcome A' × Proof F G)
    (construction : ∀ proof,
      compiled proof = image <$> transform context historyQuery validator initial proof)
    (accepts : A → Prop) (accepts' : A' → Prop)
    (preserves : ∀ result, Accepted accepts' (image result).1 → Accepted accepts result.1)
    (prover : OracleComp (FieldOracle F G) (Proof F G)) :
    Pr{let result ← (simulateQ randomOracle (prover >>= compiled)).run' ∅}[
      Accepted accepts' result.1] ≤
      Pr{let result ← (simulateQ randomOracle
        (experiment context validator initial prover)).run' ∅}[Accepted accepts result.1] := by
  have imaged : (prover >>= compiled) = image <$> experiment context validator initial prover := by
    rw [experiment, map_bind]
    exact congrArg (prover >>= ·) (funext construction)
  have mapped : (simulateQ randomOracle
      (image <$> experiment context validator initial prover)).run' ∅ =
        image <$>
          (simulateQ randomOracle (experiment context validator initial prover)).run' ∅ := by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [imaged, mapped, prEvent_map]
  exact prEvent_mono _ _ _ fun result accepted => preserves result accepted

/-- A final projection of the validator's result: the transform of
`validator.bind (done ∘ f)` accepts with `accepts` exactly as often as the
transform of `validator` accepts with `accepts ∘ f`. -/
theorem acceptance_bind_done {A' : Type} (context : Context)
    (validator : PIR.Proc (Actions F G) A) (f : A → A') (initial : History F G)
    (prover : OracleComp (FieldOracle F G) (Proof F G)) (accepts : A' → Prop) :
    Pr{let result ← (simulateQ randomOracle (experiment context
        (validator.bind fun value => .done (f value)) initial prover)).run' ∅}[
      Accepted accepts result.1] =
      Pr{let result ← (simulateQ randomOracle
        (experiment context validator initial prover)).run' ∅}[
        Accepted (fun value => accepts (f value)) result.1] := by
  have imaged : experiment context (validator.bind fun value => .done (f value)) initial prover =
      (fun result => (mapOutcome f result.1, result.2)) <$>
        experiment context validator initial prover := by
    rw [experiment, experiment, map_bind]
    exact congrArg (prover >>= ·)
      (funext fun proof => transform_bind_done context historyQuery f validator initial proof)
  have mapped : (simulateQ randomOracle ((fun result => (mapOutcome f result.1, result.2)) <$>
      experiment context validator initial prover)).run' ∅ =
        (fun result => (mapOutcome f result.1, result.2)) <$>
          (simulateQ randomOracle (experiment context validator initial prover)).run' ∅ := by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [imaged, mapped, prEvent_map]
  refine prEvent_congr _ _ _ fun result => ?_
  rcases result with ⟨outcome, rest⟩
  cases outcome <;> rfl

omit [SampleableType F] in
/-- A final projection of each statement's validator result in the adaptive
experiment moves into the acceptance predicate, together with any event on the
chosen statement. -/
theorem adaptive_acceptance_bind_done {A' : Type} [SampleableType B] (context : Context)
    (decode : B → F) (validator : Stmt → PIR.Proc (Actions F G) A) (f : A → A')
    (initial : Stmt → History F G) (prover : OracleComp (Oracle F G B) (Stmt × Proof F G))
    (event : Stmt → Prop) (accepts : A' → Prop) :
    Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context decode
        (fun statement => (validator statement).bind fun value => .done (f value)) initial
        prover)).run' ∅}[event result.1 ∧ Accepted accepts result.2.1] =
      Pr{let result ← (simulateQ randomOracle
        (adaptiveExperiment context decode validator initial prover)).run' ∅}[
        event result.1 ∧ Accepted (fun value => accepts (f value)) result.2.1] := by
  have imaged : adaptiveExperiment context decode
      (fun statement => (validator statement).bind fun value => .done (f value)) initial prover =
      (fun result => (result.1, (mapOutcome f result.2.1, result.2.2))) <$>
        adaptiveExperiment context decode validator initial prover := by
    rw [adaptiveExperiment, adaptiveExperiment, map_bind]
    refine congrArg (prover >>= ·) (funext fun claimed => ?_)
    rw [transform_bind_done context (decodedQuery decode) f (validator claimed.1)
      (initial claimed.1) claimed.2, Functor.map_map, Functor.map_map]
  have mapped : (simulateQ randomOracle
      ((fun result => (result.1, (mapOutcome f result.2.1, result.2.2))) <$>
        adaptiveExperiment context decode validator initial prover)).run' ∅ =
      (fun result => (result.1, (mapOutcome f result.2.1, result.2.2))) <$>
        (simulateQ randomOracle
          (adaptiveExperiment context decode validator initial prover)).run' ∅ := by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [imaged, mapped, prEvent_map]
  refine prEvent_congr _ _ _ fun result => ?_
  rcases result with ⟨statement, outcome, rest⟩
  cases outcome <;> rfl

end Fixed

end ZkcSecurity.FiatShamir
