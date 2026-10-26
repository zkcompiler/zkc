module

public import ZkcSecurity.FiatShamir.Sampling
public import Zkc.Construction.Uniform.Soundness
public import ZkcSecurity.VCVio.Pruning

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
(`Balanced`), and one whose events are at most `factor` times the uniform
field's multiplies the error by `factor` (`adaptive_soundness_dominated`; a
bijective decoding keeps it, `adaptive_soundness_exact`). The prover may also
choose the statement after its queries, when the initial history determines the
statement (`Determined`); the transform then runs the statement's validator from
the statement's initial history (`adaptive_soundness`). Private randomness drawn
before the oracle computation is a distribution over provers
(`randomized_soundness`).

Compiled verifiers reach these bounds through their relation to the transform.
One that is an outcome image of the transform, accepting only where the
transform accepts, accepts no more often (`acceptance_le_of_image`, fixed
statement). A final projection of the validator's result moves into the
acceptance predicate, for fixed and adaptive statements (`acceptance_bind_done`,
`adaptive_acceptance_bind_done`).

The theorems are instances of the typed-site theorems of
`ZkcSecurity.FiatShamir.Typed`. The common participant actions form a transcript
interface (`interface`) whose transform is `Zkc.Construction.transform` with the
decoded oracle as challenge function (`transform_eq`), and a round-by-round
certificate for uniform field challenges is a certificate over that interface
with the same error at every challenge occurrence, corrected by the decoding
(`RoundByRound.balanced`, `RoundByRound.dominated`).
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

/-- At most `budget` challenge queries on every path, for every reply. -/
def QueryBound : PIR.Process (Actions F G) A → ℕ → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call (.receive _ _ _) next, budget => ∀ value, QueryBound (next value) budget
  | .call (.send _ _ _) next, budget => QueryBound (next ()) budget
  | .call (.query _ _ _) next, budget =>
      0 < budget ∧ ∀ challenge, QueryBound (next challenge) (budget - 1)

theorem QueryBound.mono :
    ∀ (process : PIR.Process (Actions F G) A) {budget larger : ℕ},
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
def experiment (context : Context) (validator : PIR.Process (Actions F G) A)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) :
    OracleComp (FieldOracle F G) (PIR.Outcome A × Proof F G) :=
  prover >>= fun proof => transform context historyQuery validator initial proof

/-- The prover chooses a statement and a proof; the transform runs that
statement's validator from that statement's initial history. -/
def adaptiveExperiment (context : Context) (decode : B → F)
    (validator : Stmt → PIR.Process (Actions F G) A) (initial : Stmt → History F G)
    (prover : OracleComp (Oracle F G B) (Stmt × Proof F G)) :
    OracleComp (Oracle F G B) (Stmt × (PIR.Outcome A × Proof F G)) :=
  prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
    transform context (decodedQuery decode) (validator claimed.1) (initial claimed.1) claimed.2

/-- The initial histories determine the statements (`Zkc.Transcript.Determined`
at typed histories): when two statements' initial histories, each followed by
some events, are equal, the statements are equal. -/
abbrev Determined (initial : Stmt → History F G) : Prop :=
  Zkc.Transcript.Determined initial

section RoundByRound
variable [SampleableType F]

/-- Round-by-round soundness of validators over the common participant actions:
a doomed set of residual processes that received or sent messages cannot leave,
that contains no accepting result, and that a fresh uniform challenge leaves
with probability at most `error`. -/
structure RoundByRound (accepts : A → Prop) (error : ENNReal) where
  doomed : PIR.Process (Actions F G) A → Prop
  done : ∀ value, doomed (.done value) → ¬ accepts value
  receive : ∀ (ty : Ty) (site : String) (sender : Nat)
    (next : ScalarValue F G ty → PIR.Process (Actions F G) A),
    doomed (.call (.receive ty site sender) next) → ∀ value, doomed (next value)
  send : ∀ (ty : Ty) (site : String) (receiver : Nat) (sent : ScalarValue F G ty)
    (next : Unit → PIR.Process (Actions F G) A),
    doomed (.call (.send site receiver sent) next) → doomed (next ())
  query : ∀ (site : String) (op : services.Op)
    (arguments : Values (ScalarValue F G) (services.arguments op))
    (next : F → PIR.Process (Actions F G) A),
    doomed (.call (.query site op arguments) next) →
      Pr{let challenge ← $ᵗ F}[¬ doomed (next challenge)] ≤ error

/-- The local obligation of a doomed set at one residual. -/
def Step (doomed : PIR.Process (Actions F G) A → Prop) (accepts : A → Prop) (error : ENNReal) :
    PIR.Process (Actions F G) A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call (.receive _ _ _) next => ∀ value, doomed (next value)
  | .call (.send _ _ _) next => doomed (next ())
  | .call (.query _ _ _) next => Pr{let challenge ← $ᵗ F}[¬ doomed (next challenge)] ≤ error

/-- Enlarging the doomed set keeps every local obligation. -/
theorem Step.mono {accepts : A → Prop} {error : ENNReal}
    {small large : PIR.Process (Actions F G) A → Prop}
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
    (doomed : PIR.Process (Actions F G) A → Prop)
    (step : ∀ process, doomed process → Step doomed accepts error process) :
    RoundByRound (F := F) (G := G) accepts error where
  doomed := doomed
  done _ member := step _ member
  receive _ _ _ _ member := step _ member
  send _ _ _ _ _ member := step _ member
  query _ _ _ _ member := step _ member


end RoundByRound

section Interface

/-- The transcript interface of the common participant actions: a receive
absorbs its message occurrence with the payload and recovers the payload's value
at the expected type, a send absorbs its message occurrence with the sent value
(refusing a value without a payload), and every query absorbs its challenge
occurrence and decodes the oracle answer with `decode`, which never refuses. It
is the construction's interface `Zkc.Construction.Context.interface` with the
field answers read through `decode` (`interface_eq_mapRaw`). -/
def interface (context : Context) (decode : B → F) :
    Typed.Interface (Actions F G) (Event F G) (Payload F G) (fun _ => B)
  | .receive ty site sender =>
      .receive (fun payload => .message (context.message site sender context.validator) payload)
        (context.receivedValue ty site sender)
  | .send (ty := ty) site receiver sent =>
      match Payload.ofValue ty sent with
      | some payload =>
          .send (.message (context.message site context.validator receiver) payload) ()
      | none => .refuse
  | .query site field _ =>
      .query (.challenge (context.query site (.draw field))) fun raw => some (decode raw)

theorem received_message (context : Context) (ty : Ty) (site : String) (sender : Nat)
    (payload : Payload F G) :
    context.receivedValue ty site sender (.message (context.message site sender context.validator)
      payload) = payload.value ty := by
  simp [Context.receivedValue]

/-- The interface is the construction's interface with the field answers read
through `decode`. -/
theorem interface_eq_mapRaw (context : Context) (decode : B → F) :
    interface (G := G) context decode = context.interface.mapRaw fun _ => decode := by
  funext operation
  cases operation with
  | receive ty site sender => rfl
  | query site field arguments => rfl
  | send site receiver sent =>
      simp only [interface, Zkc.Transcript.Interface.mapRaw, Context.interface]
      cases Payload.ofValue _ sent <;> rfl

/-- The transform of the participant actions is the transform over their
interface, with the decoded oracle as challenge function. -/
theorem transform_eq (context : Context) (decode : B → F) :
    ∀ (process : PIR.Process (Actions F G) A) (history : History F G) (proof : Proof F G),
      transform context (decodedQuery decode) process history proof =
        Typed.transform (interface context decode) Typed.ask process history proof := by
  intro process history proof
  rw [interface_eq_mapRaw, Zkc.Transcript.transform_mapRaw, transform_eq_transcript]
  congr 1

/-- The query count of a participant process is its query count over the
interface. -/
theorem QueryBound.typed (context : Context) (decode : B → F) :
    ∀ (process : PIR.Process (Actions F G) A) (budget : ℕ), QueryBound process budget →
      Typed.QueryBound (interface context decode) process budget
  | .done _, _, _ => trivial
  | .halt _, _, _ => trivial
  | .call (.receive _ _ _) next, budget, bounded => fun value =>
      QueryBound.typed context decode (next value) budget (bounded value)
  | .call (.send (ty := ty) _ _ sent) next, budget, bounded => by
      simp only [Typed.QueryBound, interface]
      cases Payload.ofValue ty sent with
      | none => trivial
      | some payload => exact QueryBound.typed context decode (next ()) budget bounded
  | .call (.query _ _ _) next, budget, bounded =>
      ⟨bounded.1, fun reply => QueryBound.typed context decode _ (budget - 1) (bounded.2 _)⟩

variable [SampleableType F] [SampleableType B]

/-- A certificate over the interface from a round-by-round certificate and a
bound `escape` that turns every escape bound under uniform field challenges into
one under decoded answers. -/
def RoundByRound.typed {accepts : A → Prop} {error : ENNReal} (bound : ENNReal)
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F)
    (escape : ∀ event : F → Prop, Pr{let challenge ← $ᵗ F}[event challenge] ≤ error →
      Pr{let answer ← $ᵗ B}[event (decode answer)] ≤ bound) :
    Typed.Certificate (interface (G := G) context decode) accepts (fun _ => bound) where
  doomed := certificate.doomed
  step process member := by
    cases process with
    | done value => exact certificate.done value member
    | halt stop => trivial
    | call operation next =>
        cases operation with
        | receive ty site sender => exact certificate.receive ty site sender next member
        | send site receiver sent =>
            simp only [Typed.Step, interface]
            cases Payload.ofValue _ sent with
            | none => trivial
            | some payload => exact certificate.send _ site receiver sent next member
        | query site op arguments =>
            refine le_trans (le_of_eq (prEvent_congr _ _
              (fun raw => ¬ certificate.doomed (next (decode raw))) fun raw => ?_))
              (escape _ (certificate.query site op arguments next member))
            exact ⟨fun ⟨_, decoded, outside⟩ => by
                cases Option.some.inj decoded
                exact outside,
              fun outside => ⟨_, rfl, outside⟩⟩

/-- Balanced decoding adds its loss to every site's error. -/
noncomputable def RoundByRound.balanced {accepts : A → Prop} {error loss : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (balanced : Balanced decode loss) :
    Typed.Certificate (interface (G := G) context decode) accepts (fun _ => error + loss) :=
  certificate.typed (error + loss) context decode fun event bounded =>
    (balanced event).trans (add_le_add_left bounded loss)

/-- Dominated decoding multiplies every site's error by its factor. -/
noncomputable def RoundByRound.dominated {accepts : A → Prop} {error factor : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (dominated : Dominated decode factor) :
    Typed.Certificate (interface (G := G) context decode) accepts (fun _ => factor * error) :=
  certificate.typed (factor * error) context decode fun event bounded =>
    dominated.escape_le event bounded

omit [SampleableType F] [SampleableType B] in
/-- The adaptive experiment is the experiment over the interface. -/
theorem adaptiveExperiment_eq (context : Context) (decode : B → F)
    (validator : Stmt → PIR.Process (Actions F G) A) (initial : Stmt → History F G)
    (prover : OracleComp (Oracle F G B) (Stmt × Proof F G)) :
    adaptiveExperiment context decode validator initial prover =
      Typed.experiment (interface context decode) validator initial prover := by
  unfold adaptiveExperiment Typed.experiment
  exact congrArg (prover >>= ·) (funext fun claimed => by rw [transform_eq])

omit [SampleableType F] [SampleableType B] in
/-- The fixed-statement experiment is the experiment over the interface with
undecoded field answers. -/
theorem experiment_eq (context : Context) (validator : PIR.Process (Actions F G) A)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) :
    experiment context validator initial prover =
      Typed.fixedExperiment (interface context id) validator initial prover := by
  unfold experiment Typed.fixedExperiment
  rw [← decodedQuery_id]
  exact congrArg (prover >>= ·)
    (funext fun proof => transform_eq context id validator initial proof)

end Interface



section Adaptive
variable [DecidableEq F] [DecidableEq G] [SampleableType F] [SampleableType B]

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
    (validator : Stmt → PIR.Process (Actions F G) A) (initial : Stmt → History F G)
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
  rw [adaptiveExperiment_eq]
  exact Typed.adaptive_soundness (certificate.balanced context decode balanced) (fun _ => le_rfl)
    validator initial determined falseStatement doomedValidator budget
    (fun statement => QueryBound.typed context decode _ budget (validatorBound statement))
    prover queries proverBound

/-- Fiat–Shamir soundness with adaptively chosen statements and challenges whose
decoding is dominated by `factor`: every event of the decoded challenge is at
most `factor` times as likely as under the uniform field, for example when
every point has probability at most `factor / |F|`. The round error is
multiplied by the factor instead of being increased by an additive loss. -/
theorem adaptive_soundness_dominated {accepts : A → Prop} {error factor : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (dominated : Dominated decode factor)
    (validator : Stmt → PIR.Process (Actions F G) A) (initial : Stmt → History F G)
    (determined : Determined initial) (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, QueryBound (validator statement) budget)
    (prover : OracleComp (Oracle F G B) (Stmt × Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (adaptiveExperiment context decode validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤
      (queries + budget) * (factor * error) := by
  rw [adaptiveExperiment_eq]
  exact Typed.adaptive_soundness (certificate.dominated context decode dominated)
    (fun _ => le_rfl) validator initial determined falseStatement doomedValidator budget
    (fun statement => QueryBound.typed context decode _ budget (validatorBound statement))
    prover queries proverBound

/-- Fiat–Shamir soundness with adaptively chosen statements and exactly uniform
decoded challenges: a bijective decoding keeps the round error unchanged. -/
theorem adaptive_soundness_exact [Fintype F] [Fintype B] {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (decode : B → F) (bijective : Function.Bijective decode)
    (validator : Stmt → PIR.Process (Actions F G) A) (initial : Stmt → History F G)
    (determined : Determined initial) (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, QueryBound (validator statement) budget)
    (prover : OracleComp (Oracle F G B) (Stmt × Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (adaptiveExperiment context decode validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ (queries + budget) * error := by
  simpa only [one_mul] using adaptive_soundness_dominated certificate context decode
    (dominated_of_bijective bijective) validator initial determined falseStatement
    doomedValidator budget validatorBound prover queries proverBound

end Adaptive

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
    (validator : PIR.Process (Actions F G) A) (doomedValidator : certificate.doomed validator)
    (budget : ℕ) (validatorBound : QueryBound validator budget) (initial : History F G)
    (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (experiment context validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + budget) * error := by
  rw [experiment_eq]
  simpa only [add_zero] using Typed.soundness (certificate.balanced context id balanced_id)
    (fun _ => le_rfl) validator doomedValidator budget
    (QueryBound.typed context id validator budget validatorBound) initial prover queries
    proverBound

/-- Private randomness sampled before the oracle computation: every prover in
the support of `provers` is bounded by `queries`, so the mixture inherits the
bound. -/
theorem randomized_soundness {accepts : A → Prop} {error : ENNReal}
    (certificate : RoundByRound (F := F) (G := G) accepts error) (context : Context)
    (validator : PIR.Process (Actions F G) A) (doomedValidator : certificate.doomed validator)
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
    (validator : PIR.Process (Actions F G) A) (initial : History F G)
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
  exact ZkcSecurity.VCVio.Pruning.prEvent_le_of_image randomOracle image
    (event := fun result => Accepted accepts' result.1)
    (idealEvent := fun result => Accepted accepts result.1) preserves imaged ∅

/-- A final projection of the validator's result: the transform of
`validator.bind (done ∘ f)` accepts with `accepts` exactly as often as the
transform of `validator` accepts with `accepts ∘ f`. -/
theorem acceptance_bind_done {A' : Type} (context : Context)
    (validator : PIR.Process (Actions F G) A) (f : A → A') (initial : History F G)
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
    (decode : B → F) (validator : Stmt → PIR.Process (Actions F G) A) (f : A → A')
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
