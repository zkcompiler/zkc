module

public import ZkcSecurity.FiatShamir.Interface
public import ZkcSecurity.FiatShamir.Keyed

@[expose] public section

/-! Fiat–Shamir soundness over typed query sites, with an error per site.

The ideal experiment is the one of `ZkcSecurity.FiatShamir.Soundness`, over any
transcript interface: a prover makes arbitrary adaptive queries to a lazily
sampled random oracle on all event histories, starting from an empty cache, and
outputs a statement and a proof; the transform of that statement's validator
answers each of its queries with the same oracle at the history ending with the
query's occurrence, read in the occurrence's raw type (`ask`). The oracle
answers a history `key` with a uniform value of its range `R key`. Every query
of the whole execution counts, including repeated and cached ones.

A certificate (`Certificate`) is a doomed set of residual validator processes
that received and sent messages cannot leave and that contains no accepting
result. From a doomed query, the site's own decoding of a fresh uniform raw
answer of its occurrence yields a value that leaves the doomed set with
probability at most the error of the query's absorbed occurrence; a refused
decoding stops and never escapes. The escape bound is stated for the decoded
law of each site, so sampling corrections are part of the site's error: a
decoding whose successful values are dominated by a factor times the ideal law
multiplies the site's ideal-law error by that factor, and an additive loss adds
to it (`ZkcSecurity.FiatShamir.Sampling`).

`adaptive_soundness_weighted` charges every oracle key the error of its last
event. If the prover's queries charge at most `proverCost` on every path and
every validator's queries at most `validatorCost`, a false statement is accepted
with probability at most `proverCost + validatorCost`. With all errors at most
`bound`, `queries` prover queries and `budget` validator queries this is
`(queries + budget) * bound` (`adaptive_soundness`). `soundness_weighted` and
`soundness` are the fixed-statement forms; `randomized_soundness_weighted` and
`randomized_adaptive_soundness_weighted` add private randomness drawn before the
oracle computation.

A per-key charge `charge : List E → E → ENNReal` generalizes the error per
occurrence. A charged certificate (`ChargedCertificate`), the endpoint
certificate, has a doomed set of pairs of an absorbed history and a residual,
and bounds a doomed query's escape after the history `preceding` by
`charge preceding event`, so the error may depend on the whole key, for example
on a loop iteration the history determines or on operands carried in the
occurrence: one residual shape reached at two rounds is doomed at each round's
history with that round's error. The argument uses a doomed pair only where
replay of a validator along the history reaches the residual (`BadKeyAt`). The
charged theorems (`adaptive_soundness_charged`, `soundness_charged`,
`randomized_soundness_charged`, `randomized_adaptive_soundness_charged`) charge
every oracle key `keyCharge charge`; the theorems with an error per occurrence
are their instances at the charge that ignores the history
(`Certificate.charged`, `keyCharge_const`), and the uniform bounds follow from
those. The richer charge discharges neither obligation of the weighted bound:
the all-table resampling bound and the pathwise weighted budget are still
proved for each certificate.

Every bound is one application of the keyed endpoint
(`ZkcSecurity.FiatShamir.KeyedCertificate.soundness`) to the keyed certificate a
charged certificate gives for the experiment (`ChargedCertificate.keyed`,
`ChargedCertificate.keyedFixed`). A key is bad when replaying a statement's
validator along the key reaches a doomed query whose occurrence is the key's
last event and whose decoded answer at the key leaves the doomed set. Replay
reads the oracle only at shorter histories and the key determines the
statement, so resampling the key's answer leaves the replayed residual
unchanged; an accepting run from a doomed validator must leave the doomed set at
one of its own queries, which are in the query log.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Typed
open OracleComp OracleSpec

variable {I : PIR.Signature} {E P A Stmt : Type} {Raw : E → Type} {R : List E → Type}

section Certificate
variable [∀ event, SampleableType (Raw event)]

/-- The local obligation of a doomed set at one residual: a doomed result does
not accept, doomed receives and sends stay doomed, and a doomed query's decoded
fresh raw answer of its occurrence leaves the doomed set with probability at
most the error of its occurrence. -/
def Step (absorb : Interface I E P Raw) (doomed : PIR.Proc I A → Prop) (accepts : A → Prop)
    (error : E → ENNReal) : PIR.Proc I A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call operation next =>
      match absorb operation with
      | .receive _ _ => ∀ value, doomed (next value)
      | .send _ value => doomed (next value)
      | .query event decode =>
          Pr{let raw ← $ᵗ (Raw event)}[∃ value, decode raw = some value ∧ ¬ doomed (next value)] ≤
            error event
      | .refuse => True

/-- Round-by-round soundness over a transcript interface, with an error per
absorbed query occurrence: a doomed set of residual processes whose every
member meets its local obligation `Step`. -/
structure Certificate (absorb : Interface I E P Raw) (accepts : A → Prop) (error : E → ENNReal) where
  doomed : PIR.Proc I A → Prop
  step : ∀ process, doomed process → Step absorb doomed accepts error process

variable (absorb : Interface I E P Raw)

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
        refine (prEvent_mono _ _
          (fun raw => ∃ value, decode raw = some value ∧ ¬ small (next value))
          (fun _ escaping => ?_)).trans step
        obtain ⟨value, decoded, outside⟩ := escaping
        exact ⟨value, decoded, fun inside => outside (included _ inside)⟩
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

/-- The local obligation, with a per-key charge, of a doomed set indexed by the
absorbed history, at one residual reached after `history`: a doomed result does
not accept; after a receive whose event recovers a reply, and after a send, the
residual is doomed at the extended history; and a doomed query's decoded fresh
raw answer leaves the doomed set at the extended history with probability at
most `charge history event`, the charge of the query's key. Indexing the doomed
set by the history lets one residual shape carry a different error at each
place it is reached, for example at each round of a loop whose occurrence
carries no iteration coordinate. -/
def ChargedStep (doomed : List E → PIR.Proc I A → Prop) (accepts : A → Prop)
    (charge : List E → E → ENNReal) (history : List E) : PIR.Proc I A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call operation next =>
      match absorb operation with
      | .receive event recover => ∀ message value, recover (event message) = some value →
          doomed (history ++ [event message]) (next value)
      | .send event value => doomed (history ++ [event]) (next value)
      | .query event decode =>
          Pr{let raw ← $ᵗ (Raw event)}[
            ∃ value, decode raw = some value ∧
              ¬ doomed (history ++ [event]) (next value)] ≤ charge history event
      | .refuse => True

/-- Round-by-round soundness over a transcript interface with a per-key charge,
the endpoint certificate: a set of doomed pairs of an absorbed history and a
residual process, whose every member meets its local obligation `ChargedStep`.
The security theorems use a pair only where replaying a validator along the
history reaches the residual. -/
structure ChargedCertificate (accepts : A → Prop) (charge : List E → E → ENNReal) where
  doomed : List E → PIR.Proc I A → Prop
  step : ∀ history process, doomed history process →
    ChargedStep absorb doomed accepts charge history process

/-- Enlarging the doomed set keeps every charged local obligation. -/
theorem ChargedStep.mono {accepts : A → Prop} {charge : List E → E → ENNReal}
    {small large : List E → PIR.Proc I A → Prop}
    (included : ∀ history process, small history process → large history process)
    (history : List E) :
    ∀ process, ChargedStep absorb small accepts charge history process →
      ChargedStep absorb large accepts charge history process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [ChargedStep, absorbed] at step ⊢
        exact fun message value recovered => included _ _ (step message value recovered)
      · simp only [ChargedStep, absorbed] at step ⊢
        exact included _ _ step
      · simp only [ChargedStep, absorbed] at step ⊢
        refine (prEvent_mono _ _
          (fun raw => ∃ value, decode raw = some value ∧ ¬ small (history ++ [event]) (next value))
          (fun _ escaping => ?_)).trans step
        obtain ⟨value, decoded, outside⟩ := escaping
        exact ⟨value, decoded, fun inside => outside (included _ _ inside)⟩
      · simp only [ChargedStep, absorbed]

/-- Larger charges keep every local obligation. -/
theorem ChargedStep.mono_charge {doomed : List E → PIR.Proc I A → Prop} {accepts : A → Prop}
    {charge larger : List E → E → ENNReal}
    (le : ∀ preceding event, charge preceding event ≤ larger preceding event)
    (history : List E) :
    ∀ process, ChargedStep absorb doomed accepts charge history process →
      ChargedStep absorb doomed accepts larger history process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [ChargedStep, absorbed] at step ⊢
        exact step
      · simp only [ChargedStep, absorbed] at step ⊢
        exact step
      · simp only [ChargedStep, absorbed] at step ⊢
        exact step.trans (le history event)
      · simp only [ChargedStep, absorbed]

/-- A charged certificate with larger charges. -/
def ChargedCertificate.weaken {accepts : A → Prop} {charge larger : List E → E → ENNReal}
    (certificate : ChargedCertificate absorb accepts charge)
    (le : ∀ preceding event, charge preceding event ≤ larger preceding event) :
    ChargedCertificate absorb accepts larger where
  doomed := certificate.doomed
  step history process member :=
    ChargedStep.mono_charge absorb le history process (certificate.step history process member)

/-- A local obligation with an error per occurrence is the charged obligation,
at every history, of the same doomed set read at every history and the charge
that ignores the history. -/
theorem Step.charged {doomed : PIR.Proc I A → Prop} {accepts : A → Prop} {error : E → ENNReal}
    (history : List E) :
    ∀ process, Step absorb doomed accepts error process →
      ChargedStep absorb (fun _ process => doomed process) accepts (fun _ event => error event)
        history process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Step, absorbed] at step
        simp only [ChargedStep, absorbed]
        exact fun _ value _ => step value
      · simp only [Step, absorbed] at step
        simp only [ChargedStep, absorbed]
        exact step
      · simp only [Step, absorbed] at step
        simp only [ChargedStep, absorbed]
        exact step
      · simp only [ChargedStep, absorbed]

/-- A certificate with an error per occurrence is a charged certificate for the
charge that ignores the history, whose doomed set ignores the history too. -/
def Certificate.charged {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Certificate absorb accepts error) :
    ChargedCertificate absorb accepts (fun _ event => error event) where
  doomed _ process := certificate.doomed process
  step history process member :=
    Step.charged absorb history process (certificate.step process member)

end Certificate

section Bad
variable [DecidableEq E]

/-- The raw answer `raw` to a doomed query with occurrence `event` decodes to a
value that leaves the doomed set. Only query nodes can escape. -/
def Escapes (absorb : Interface I E P Raw) (doomed : PIR.Proc I A → Prop) :
    PIR.Proc I A → (event : E) → Raw event → Prop
  | .call operation next, event, raw =>
      ∃ decode, absorb operation = .query event decode ∧ doomed (.call operation next) ∧
        ∃ value, decode raw = some value ∧ ¬ doomed (next value)
  | _, _, _ => False

/-- `Escapes` for a doomed set indexed by the absorbed history: the residual is
doomed at `preceding`, and the decoded answer leaves the doomed set at
`preceding ++ [event]`. -/
def EscapesAt (absorb : Interface I E P Raw) (doomed : List E → PIR.Proc I A → Prop) :
    PIR.Proc I A → (event : E) → (preceding : List E) → Raw event → Prop
  | .call operation next, event, preceding, raw =>
      ∃ decode, absorb operation = .query event decode ∧ doomed preceding (.call operation next) ∧
        ∃ value, decode raw = some value ∧ ¬ doomed (preceding ++ [event]) (next value)
  | _, _, _, _ => False

variable [ReadsByOccurrence R Raw]

/-- A bad oracle key: for some statement, replaying its validator from its
initial history along the key's events before the last one reaches a residual
whose query, answered by the table at the key, escapes the doomed set. -/
def BadKey (absorb : Interface I E P Raw) (doomed : PIR.Proc I A → Prop)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (key : List E)
    (table : (key : List E) → R key) : Prop :=
  ∃ statement events observed process, key = initial statement ++ events ++ [observed] ∧
    replay absorb (readTable table) (validator statement) (initial statement) events = some process ∧
    Escapes absorb doomed process observed (readTable table (initial statement ++ events) observed)

/-- `BadKey` for a doomed set indexed by the absorbed history: replaying a
statement's validator along the key's events reaches a residual, doomed at the
replayed history, whose query escapes at the key. The pairing of residual and
history comes from the replay, not from an honest execution. -/
def BadKeyAt (absorb : Interface I E P Raw) (doomed : List E → PIR.Proc I A → Prop)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (key : List E)
    (table : (key : List E) → R key) : Prop :=
  ∃ statement events observed process, key = initial statement ++ events ++ [observed] ∧
    replay absorb (readTable table) (validator statement) (initial statement) events = some process ∧
    EscapesAt absorb doomed process observed (initial statement ++ events)
      (readTable table (initial statement ++ events) observed)

omit [DecidableEq E] [ReadsByOccurrence R Raw] in
/-- A doomed set that ignores the history escapes as `Escapes` does. -/
theorem escapesAt_const (absorb : Interface I E P Raw) (doomed : PIR.Proc I A → Prop)
    (process : PIR.Proc I A) (event : E) (preceding : List E) (raw : Raw event) :
    EscapesAt absorb (fun _ process => doomed process) process event preceding raw ↔
      Escapes absorb doomed process event raw := by
  cases process <;> exact Iff.rfl

/-- A doomed set that ignores the history makes the same keys bad as `BadKey`. -/
theorem badKeyAt_const (absorb : Interface I E P Raw) (doomed : PIR.Proc I A → Prop)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (key : List E)
    (table : (key : List E) → R key) :
    BadKeyAt absorb (fun _ process => doomed process) validator initial key table ↔
      BadKey absorb doomed validator initial key table := by
  simp only [BadKeyAt, BadKey, escapesAt_const]

omit [DecidableEq E] [ReadsByOccurrence R Raw] in
/-- Two decompositions of one key agree. -/
theorem key_shape {initial events events' : List E} {observed observed' : E}
    (same : initial ++ events ++ [observed] = initial ++ events' ++ [observed']) :
    events = events' ∧ observed = observed' := by
  rw [List.append_assoc, List.append_assoc] at same
  obtain ⟨prefixes, lasts⟩ := List.append_inj' (List.append_cancel_left same) rfl
  exact ⟨prefixes, List.singleton_inj.mp lasts⟩

/-- The replayed residual before a key does not depend on the answer at the key. -/
theorem replay_update (absorb : Interface I E P Raw) (table : (key : List E) → R key)
    (validator : PIR.Proc I A) (initial events : List E) (observed : E)
    (raw : R (initial ++ events ++ [observed])) :
    replay absorb (readTable (Function.update table (initial ++ events ++ [observed]) raw))
        validator initial events =
      replay absorb (readTable table) validator initial events := by
  refine Zkc.Transcript.replay_congr absorb _ events validator initial
    fun preceding event shorter => ?_
  unfold readTable
  rw [Function.update_of_ne]
  intro same
  have := congrArg List.length same
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

variable [∀ key, SampleableType (R key)] [∀ event, SampleableType (Raw event)]

omit [DecidableEq E] [ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)] in
/-- A fixed residual, doomed at a fixed history, escapes at a fresh raw answer
with probability at most the charge of its key. -/
theorem escapes_le_charged {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (process : PIR.Proc I A) (observed : E) (preceding : List E) :
    Pr{let raw ← $ᵗ (Raw observed)}[
      EscapesAt absorb certificate.doomed process observed preceding raw] ≤
        charge preceding observed := by
  classical
  have impossible :
      (∀ raw, ¬ EscapesAt absorb certificate.doomed process observed preceding raw) →
        Pr{let raw ← $ᵗ (Raw observed)}[
          EscapesAt absorb certificate.doomed process observed preceding raw] ≤
            charge preceding observed :=
    fun never => (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le
  cases process with
  | done value => exact impossible fun _ escapes => escapes
  | halt stop => exact impossible fun _ escapes => escapes
  | call operation next =>
      by_cases relevant : ∃ decode, absorb operation = .query observed decode ∧
          certificate.doomed preceding (.call operation next)
      · obtain ⟨decode, absorbed, doomed⟩ := relevant
        have step := certificate.step _ _ doomed
        simp only [ChargedStep, absorbed] at step
        refine (prEvent_mono _ _
          (fun raw => ∃ value, decode raw = some value ∧
            ¬ certificate.doomed (preceding ++ [observed]) (next value))
          (fun raw escapes => ?_)).trans step
        obtain ⟨decode', absorbed', _, escaping⟩ := escapes
        rw [absorbed] at absorbed'
        obtain ⟨-, same⟩ := Zkc.Transcript.Absorption.query.inj absorbed'
        subst same
        exact escaping
      · exact impossible fun _ escapes => by
          obtain ⟨decode, absorbed, doomed, _⟩ := escapes
          exact relevant ⟨decode, absorbed, doomed⟩

omit [DecidableEq E] [ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)] in
/-- A fixed residual escapes at a fresh raw answer with probability at most the
error of the occurrence. -/
theorem escapes_le {absorb : Interface I E P Raw} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Certificate absorb accepts error) (process : PIR.Proc I A) (observed : E) :
    Pr{let raw ← $ᵗ (Raw observed)}[
      Escapes absorb certificate.doomed process observed raw] ≤ error observed :=
  (le_of_eq (prEvent_congr _ _ _ fun raw =>
    (escapesAt_const absorb certificate.doomed process observed [] raw).symm)).trans
    (escapes_le_charged certificate.charged process observed [])

/-- Resampling the answer at any key, under every background table, makes the
key bad with probability at most the charge of the key. -/
theorem badKey_resample_charged {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (key : List E) (table : (key : List E) → R key) :
    Pr{let raw ← $ᵗ (R key)}[BadKeyAt absorb certificate.doomed validator initial key
      (Function.update table key raw)] ≤ keyCharge charge key := by
  by_cases found : ∃ statement events observed process,
      key = initial statement ++ events ++ [observed] ∧
      replay absorb (readTable table) (validator statement) (initial statement) events =
        some process
  · obtain ⟨statement, events, observed, process, shape, replayed⟩ := found
    subst shape
    have reduced : ∀ raw,
        BadKeyAt absorb certificate.doomed validator initial
            (initial statement ++ events ++ [observed])
            (Function.update table (initial statement ++ events ++ [observed]) raw) →
          EscapesAt absorb certificate.doomed process observed (initial statement ++ events)
            (ReadsByOccurrence.read (initial statement ++ events) observed raw) := by
      rintro raw ⟨statement', events', observed', process', shape', replayed', escapes⟩
      have same : statement = statement' := determined _ _ (events ++ [observed])
        (events' ++ [observed']) (by simpa only [List.append_assoc] using shape')
      subst same
      obtain ⟨rfl, rfl⟩ := key_shape shape'
      rw [replay_update, replayed] at replayed'
      cases replayed'
      simpa only [readTable, Function.update_self] using escapes
    calc Pr{let raw ← $ᵗ (R (initial statement ++ events ++ [observed]))}[
            BadKeyAt absorb certificate.doomed validator initial
              (initial statement ++ events ++ [observed])
              (Function.update table (initial statement ++ events ++ [observed]) raw)]
        ≤ Pr{let raw ← $ᵗ (R (initial statement ++ events ++ [observed]))}[
            EscapesAt absorb certificate.doomed process observed (initial statement ++ events)
              (ReadsByOccurrence.read (initial statement ++ events) observed raw)] :=
          prEvent_mono _ _ _ reduced
      _ = Pr{let raw ← $ᵗ (Raw observed)}[
            EscapesAt absorb certificate.doomed process observed (initial statement ++ events)
              raw] :=
          prEvent_reads (initial statement ++ events) observed _
      _ ≤ charge (initial statement ++ events) observed :=
          escapes_le_charged certificate process observed _
      _ = keyCharge charge (initial statement ++ events ++ [observed]) :=
          (keyCharge_append_singleton charge _ observed).symm
  · have never : ∀ raw, ¬ BadKeyAt absorb certificate.doomed validator initial key
        (Function.update table key raw) := by
      rintro raw ⟨statement, events, observed, process, shape, replayed, _⟩
      subst shape
      rw [replay_update] at replayed
      exact found ⟨statement, events, observed, process, rfl, replayed⟩
    exact (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le

/-- Resampling the answer at any key, under every background table, makes the
key bad with probability at most the error of its last event. -/
theorem badKey_resample {absorb : Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (key : List E) (table : (key : List E) → R key) :
    Pr{let raw ← $ᵗ (R key)}[BadKey absorb certificate.doomed validator initial key
      (Function.update table key raw)] ≤ keyError error key := by
  have charged := badKey_resample_charged certificate.charged validator initial determined key table
  rw [keyCharge_const] at charged
  exact (le_of_eq (prEvent_congr _ _ _ fun raw =>
    (badKeyAt_const absorb certificate.doomed validator initial key _).symm)).trans charged

omit [∀ key, SampleableType (R key)] in
/-- An accepting run of the transform, against a total table, from a doomed
residual reached by replay queries a bad key. -/
theorem escape_logged_charged {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (table : (key : List E) → R key) (statement : Stmt) :
    ∀ (process : PIR.Proc I A) (events history : List E) (proof : List P),
      replay absorb (readTable table) (validator statement) (initial statement) events =
        some process →
      history = initial statement ++ events →
      certificate.doomed history process →
      Accepted accepts (transform (m := Id) absorb (readTable (Raw := Raw) table) process history proof).1 →
      ∃ query ∈ tableQueryLog (transform absorb (ask (R := R)) process history proof) table,
        BadKeyAt absorb certificate.doomed validator initial query.1 table := by
  intro process
  induction process with
  | done value =>
      intro events history proof _ _ doomed accepted
      exact absurd accepted (certificate.step _ _ doomed)
  | halt stop =>
      intro events history proof _ _ _ accepted
      exact accepted.elim
  | call operation next ih =>
      intro events history proof replayed shape doomed accepted
      have step := certificate.step _ _ doomed
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [ChargedStep, absorbed] at step
        cases proof with
        | nil =>
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed] at accepted
            exact accepted.elim
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed] at accepted
            rw [Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recovered : recover (event message) with
            | none =>
                rw [recovered] at accepted
                exact accepted.elim
            | some value =>
                rw [recovered] at accepted
                dsimp only at accepted ⊢
                apply ih value (events ++ [event message]) _ rest _
                  (by rw [shape, List.append_assoc]) (step message value recovered) accepted
                rw [Zkc.Transcript.replay_append, replayed, Option.bind_some, ← shape]
                exact Zkc.Transcript.replay_receive absorb _ absorbed history message recovered
      · simp only [ChargedStep, absorbed] at step
        rw [Zkc.Transcript.transform_send absorb _ absorbed] at accepted
        rw [Zkc.Transcript.transform_send absorb _ absorbed]
        apply ih value (events ++ [event]) _ proof _ (by rw [shape, List.append_assoc]) step
          accepted
        rw [Zkc.Transcript.replay_append, replayed, Option.bind_some, ← shape]
        exact Zkc.Transcript.replay_send absorb _ absorbed history
      · rw [Zkc.Transcript.transform_query absorb _ absorbed] at accepted
        rw [Zkc.Transcript.transform_query absorb _ absorbed, ask_bind, answer,
          tableQueryLog_query_bind]
        change Accepted accepts (match decode (readTable table history event) with
          | some value => transform (m := Id) absorb (readTable (Raw := Raw) table) (next value)
              (history ++ [event]) proof
          | none => pure (.stopped .exhausted, proof)).1 at accepted
        cases decoded : decode (readTable table history event) with
        | none =>
            rw [decoded] at accepted
            exact accepted.elim
        | some value =>
            rw [decoded] at accepted
            by_cases stays : certificate.doomed (history ++ [event]) (next value)
            · obtain ⟨query, logged, bad⟩ := ih value (events ++ [event]) _ proof
                (by
                  rw [Zkc.Transcript.replay_append, replayed, Option.bind_some, ← shape]
                  exact Zkc.Transcript.replay_query absorb _ absorbed history decoded)
                (by rw [shape, List.append_assoc]) stays accepted
              refine ⟨query, List.mem_cons_of_mem _ ?_, bad⟩
              have decoded' : decode (ReadsByOccurrence.read history event
                  (table (history ++ [event]))) = some value := decoded
              simpa only [decoded'] using logged
            · refine ⟨⟨history ++ [event], table (history ++ [event])⟩, List.mem_cons_self, ?_⟩
              subst shape
              exact ⟨statement, events, event, .call operation next, rfl, replayed, decode,
                absorbed, doomed, value, decoded, stays⟩
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed] at accepted
        exact accepted.elim

omit [∀ key, SampleableType (R key)] in
/-- An accepting run of the transform, against a total table, from a doomed
residual reached by replay queries a bad key. -/
theorem escape_logged {absorb : Interface I E P Raw} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Certificate absorb accepts error)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (table : (key : List E) → R key) (statement : Stmt) :
    ∀ (process : PIR.Proc I A) (events history : List E) (proof : List P),
      replay absorb (readTable table) (validator statement) (initial statement) events =
        some process →
      history = initial statement ++ events →
      certificate.doomed process →
      Accepted accepts (transform (m := Id) absorb (readTable (Raw := Raw) table) process history proof).1 →
      ∃ query ∈ tableQueryLog (transform absorb (ask (R := R)) process history proof) table,
        BadKey absorb certificate.doomed validator initial query.1 table := by
  intro process events history proof replayed shape doomed accepted
  obtain ⟨query, logged, bad⟩ := escape_logged_charged certificate.charged validator initial table
    statement process events history proof replayed shape doomed accepted
  exact ⟨query, logged, (badKeyAt_const absorb certificate.doomed validator initial _ _).mp bad⟩

end Bad

/-- The prover chooses a statement and a proof; the transform runs that
statement's validator from that statement's initial history. -/
def experiment (absorb : Interface I E P Raw) [ReadsByOccurrence R Raw]
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (prover : OracleComp (OracleSpec.ofFn R) (Stmt × List P)) :
    OracleComp (OracleSpec.ofFn R) (Stmt × (PIR.Outcome A × List P)) :=
  prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
    transform absorb ask (validator claimed.1) (initial claimed.1) claimed.2

/-- The prover's oracle computation followed by the transform of `validator`
from the history `initial`, sharing one oracle. -/
def fixedExperiment (absorb : Interface I E P Raw) [ReadsByOccurrence R Raw]
    (validator : PIR.Proc I A) (initial : List E)
    (prover : OracleComp (OracleSpec.ofFn R) (List P)) :
    OracleComp (OracleSpec.ofFn R) (PIR.Outcome A × List P) :=
  prover >>= fun proof => transform absorb ask validator initial proof

section Keyed
variable [DecidableEq E] [ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)]
  [∀ event, SampleableType (Raw event)]

/-- The keyed certificate of the adaptive experiment that a charged certificate
gives: keys are charged `keyCharge charge`, and a key is bad when replay of some
statement's validator along it escapes the doomed set at its last event. -/
def ChargedCertificate.keyed {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (initial statement) (validator statement))
    (prover : OracleComp (OracleSpec.ofFn R) (Stmt × List P)) :
    KeyedCertificate R (experiment absorb validator initial prover)
      (fun result => falseStatement result.1 ∧ Accepted accepts result.2.1) where
  charge := keyCharge charge
  bad := BadKeyAt absorb certificate.doomed validator initial
  resample := badKey_resample_charged certificate validator initial determined
  trace table accepted := by
    simp only [experiment, evalWithAnswerFn_bind, evalWithAnswerFn_map,
      evalWithAnswerFn_transform] at accepted
    obtain ⟨query, logged, bad⟩ := escape_logged_charged certificate validator initial table
      (evalWithAnswerFn (QueryImpl.ofFn table) prover).1
      (validator (evalWithAnswerFn (QueryImpl.ofFn table) prover).1) []
      (initial (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
      (evalWithAnswerFn (QueryImpl.ofFn table) prover).2 (by simp) (by simp)
      (doomedValidator _ accepted.1) accepted.2
    refine ⟨query, ?_, bad⟩
    rw [experiment, tableQueryLog_bind, tableQueryLog_map]
    exact List.mem_append_right _ logged

/-- The keyed certificate of the fixed-statement experiment that a charged
certificate gives. -/
def ChargedCertificate.keyedFixed {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : PIR.Proc I A) (initial : List E)
    (doomedValidator : certificate.doomed initial validator)
    (prover : OracleComp (OracleSpec.ofFn R) (List P)) :
    KeyedCertificate R (fixedExperiment absorb validator initial prover)
      (fun result => Accepted accepts result.1) where
  charge := keyCharge charge
  bad := BadKeyAt absorb certificate.doomed (fun _ : Unit => validator) (fun _ => initial)
  resample := badKey_resample_charged certificate _ _ (fun _ _ _ _ _ => rfl)
  trace table accepted := by
    simp only [fixedExperiment, evalWithAnswerFn_bind, evalWithAnswerFn_transform] at accepted
    obtain ⟨query, logged, bad⟩ := escape_logged_charged certificate (fun _ : Unit => validator)
      (fun _ => initial) table () validator [] initial
      (evalWithAnswerFn (QueryImpl.ofFn table) prover) (by simp) (by simp) doomedValidator
      accepted
    refine ⟨query, ?_, bad⟩
    rw [fixedExperiment, tableQueryLog_bind]
    exact List.mem_append_right _ logged

end Keyed

section Theorems
variable [DecidableEq E] [ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)]
  [∀ event, SampleableType (Raw event)]

/-- Fiat–Shamir soundness with adaptively chosen statements and a per-key charge.

The prover is any oracle computation on the transcript oracle; it may hold
arbitrary internal state, query any history and choose the statement after its
queries. Charging every oracle key `keyCharge charge`, the charge of its last
event after the history before it, its queries charge at most `proverCost` on
every path (repeats and cache hits included). The initial history determines the
statement. The oracle starts with an empty cache and is shared with the
transform, whose queries from the statement's initial history charge at most
`validatorCost`. A statement satisfying `falseStatement` has a doomed
validator. -/
theorem adaptive_soundness_charged {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (initial statement) (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement,
      ChargedCostBound absorb charge (validator statement) (initial statement) validatorCost)
    (prover : OracleComp (OracleSpec.ofFn R) (Stmt × List P)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyCharge charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ proverCost + validatorCost :=
  (certificate.keyed validator initial determined falseStatement doomedValidator prover).soundness
    (WorstCaseCostBound.bind proverBound fun claimed => worstCaseCostBound_map _ _ _ _
      (transform_chargedCostBound absorb charge (validator claimed.1) validatorCost
        (initial claimed.1) claimed.2 (validatorBound claimed.1)))

/-- Fiat–Shamir soundness with adaptively chosen statements and an error per
query site.

The prover is any oracle computation on the transcript oracle; it may hold
arbitrary internal state, query any history and choose the statement after its
queries. Charging every oracle key the error of its last event, its queries
charge at most `proverCost` on every path (repeats and cache hits included). The
initial history determines the statement. The oracle starts with an empty cache
and is shared with the transform, whose queries charge at most `validatorCost`.
A statement satisfying `falseStatement` has a doomed validator. -/
theorem adaptive_soundness_weighted {absorb : Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement, CostBound absorb error (validator statement) validatorCost)
    (prover : OracleComp (OracleSpec.ofFn R) (Stmt × List P)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ proverCost + validatorCost := by
  rw [← keyCharge_const] at proverBound
  exact adaptive_soundness_charged certificate.charged validator initial determined falseStatement
    doomedValidator validatorCost
    (fun statement => CostBound.charged absorb error _ validatorCost (validatorBound statement) _)
    prover proverCost proverBound

/-- Fiat–Shamir soundness with adaptively chosen statements, for a prover with
at most `queries` oracle queries and validators with at most `budget` queries
on every path, when every site's error is at most `bound`. -/
theorem adaptive_soundness {absorb : Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, QueryBound absorb (validator statement) budget)
    (prover : OracleComp (OracleSpec.ofFn R) (Stmt × List P)) (queries : ℕ)
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

/-- Fiat–Shamir soundness for a fixed statement with a per-key charge. The
prover's queries charge at most `proverCost` on every path and the validator's,
from the history `initial`, at most `validatorCost`. -/
theorem soundness_charged {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : PIR.Proc I A) (initial : List E)
    (doomedValidator : certificate.doomed initial validator) (validatorCost : ENNReal)
    (validatorBound : ChargedCostBound absorb charge validator initial validatorCost)
    (prover : OracleComp (OracleSpec.ofFn R) (List P)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyCharge charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run'
        ∅}[Accepted accepts result.1] ≤ proverCost + validatorCost :=
  (certificate.keyedFixed validator initial doomedValidator prover).soundness
    (WorstCaseCostBound.bind proverBound fun proof =>
      transform_chargedCostBound absorb charge validator validatorCost initial proof validatorBound)

/-- Fiat–Shamir soundness for a fixed statement, with an error per query site.
The prover's queries charge at most `proverCost` on every path and the
validator's at most `validatorCost`. -/
theorem soundness_weighted {absorb : Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : PIR.Proc I A) (doomedValidator : certificate.doomed validator)
    (validatorCost : ENNReal) (validatorBound : CostBound absorb error validator validatorCost)
    (initial : List E) (prover : OracleComp (OracleSpec.ofFn R) (List P)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run'
        ∅}[Accepted accepts result.1] ≤ proverCost + validatorCost := by
  rw [← keyCharge_const] at proverBound
  exact soundness_charged certificate.charged validator initial doomedValidator validatorCost
    (CostBound.charged absorb error validator validatorCost validatorBound initial) prover proverCost
    proverBound

/-- Fiat–Shamir soundness for a fixed statement: a prover with at most `queries`
oracle queries makes the transform of a doomed validator with at most `budget`
queries accept with probability at most `(queries + budget) * bound` when every
site's error is at most `bound`. -/
theorem soundness {absorb : Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound)
    (validator : PIR.Proc I A) (doomedValidator : certificate.doomed validator)
    (budget : ℕ) (validatorBound : QueryBound absorb validator budget) (initial : List E)
    (prover : OracleComp (OracleSpec.ofFn R) (List P)) (queries : ℕ)
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

/-- Private randomness sampled before the oracle computation, with a per-key
charge: every prover in the support of `provers` is bounded by `proverCost`, so
the mixture inherits the bound. -/
theorem randomized_soundness_charged {absorb : Interface I E P Raw} {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : ChargedCertificate absorb accepts charge)
    (validator : PIR.Proc I A) (initial : List E)
    (doomedValidator : certificate.doomed initial validator) (validatorCost : ENNReal)
    (validatorBound : ChargedCostBound absorb charge validator initial validatorCost)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn R) (List P))) (proverCost : ENNReal)
    (proverBound : ∀ prover ∈ support provers,
      WorstCaseCostBound prover ⟨keyCharge charge⟩ proverCost) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ proverCost + validatorCost :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    soundness_charged certificate validator initial doomedValidator validatorCost validatorBound
      prover proverCost (proverBound prover drawn)

/-- Private randomness sampled before the oracle computation: every prover in
the support of `provers` is bounded by `proverCost`, so the mixture inherits the
bound. -/
theorem randomized_soundness_weighted {absorb : Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : PIR.Proc I A) (doomedValidator : certificate.doomed validator)
    (validatorCost : ENNReal) (validatorBound : CostBound absorb error validator validatorCost)
    (initial : List E) (provers : ProbComp (OracleComp (OracleSpec.ofFn R) (List P)))
    (proverCost : ENNReal)
    (proverBound : ∀ prover ∈ support provers,
      WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (fixedExperiment absorb validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ proverCost + validatorCost := by
  simp only [← keyCharge_const] at proverBound
  exact randomized_soundness_charged certificate.charged validator initial doomedValidator
    validatorCost (CostBound.charged absorb error validator validatorCost validatorBound initial)
    provers proverCost proverBound

/-- Adaptive statements with private randomness and a per-key charge: a
mixture of provers, each choosing its statement after its queries and charging
at most `proverCost` on every path, inherits the adaptive bound. This is the
ideal side a provider simulation's translated adversary meets. -/
theorem randomized_adaptive_soundness_charged {absorb : Interface I E P Raw}
    {accepts : A → Prop} {charge : List E → E → ENNReal}
    (certificate : ChargedCertificate absorb accepts charge)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (initial statement) (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement,
      ChargedCostBound absorb charge (validator statement) (initial statement) validatorCost)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn R) (Stmt × List P))) (proverCost : ENNReal)
    (proverBound : ∀ prover ∈ support provers,
      WorstCaseCostBound prover ⟨keyCharge charge⟩ proverCost) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ proverCost + validatorCost :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    adaptive_soundness_charged certificate validator initial determined falseStatement
      doomedValidator validatorCost validatorBound prover proverCost (proverBound prover drawn)

/-- Adaptive statements with private randomness and an error per query site. -/
theorem randomized_adaptive_soundness_weighted {absorb : Interface I E P Raw}
    {accepts : A → Prop} {error : E → ENNReal} (certificate : Certificate absorb accepts error)
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E) (determined : Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement, CostBound absorb error (validator statement) validatorCost)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn R) (Stmt × List P))) (proverCost : ENNReal)
    (proverBound : ∀ prover ∈ support provers,
      WorstCaseCostBound prover ⟨keyError error⟩ proverCost) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ proverCost + validatorCost :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    adaptive_soundness_weighted certificate validator initial determined falseStatement
      doomedValidator validatorCost validatorBound prover proverCost (proverBound prover drawn)

end Theorems

end ZkcSecurity.FiatShamir.Typed
