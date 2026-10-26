module

public import Zkc.Construction.ScalarAdapter
public import Zkc.Construction.DomainBinding
public import Zkc.Construction.OriginalSimulation

@[expose] public section

/-! The retained scalar ABI as a property handler of the Domain Process.

The initial legacy history is opaque. Only the execution suffix is projected;
the key adapter runs before the existing challenge function is called. This
does not replace that oracle by a nominal random oracle. There are no
instruction cases in this module. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.DomainAdapter
open Zkc.Source
variable {F G : Type}

def embedPayload : Payload F G → Domain.Payload (Structured.uniformCarriers F G)
  | .boolean value => .boolean value
  | .field domain value => .field domain value
  | .group domain value => .group domain value

def readbackPayload : Domain.Payload (Structured.uniformCarriers F G) → Option (Payload F G)
  | ⟨.boolean, _, value⟩ => some (.boolean value)
  | ⟨.field domain, _, value⟩ => some (.field domain value)
  | ⟨.group domain, _, value⟩ => some (.group domain value)
  | _ => none

@[simp] theorem readbackPayload_embed (payload : Payload F G) :
    readbackPayload (embedPayload payload) = some payload := by cases payload <;> rfl

def readbackEvent (key : Origin → Origin) :
    Domain.Event (Structured.uniformCarriers F G) → Option (Event F G)
  | .message origin payload => (readbackPayload payload).map (.message (key origin))
  | .challenge origin => some (.challenge (key origin))
  | .publicBinding _ => none

def readbackHistory (key : Origin → Origin)
    (history : Domain.History (Structured.uniformCarriers F G)) : Option (History F G) :=
  history.mapM (readbackEvent key)

theorem readbackHistory_append (key : Origin → Origin)
    (first second : Domain.History (Structured.uniformCarriers F G)) :
    readbackHistory key (first ++ second) = (do
      let one ← readbackHistory key first
      let two ← readbackHistory key second
      pure (one ++ two)) := by simp [readbackHistory, List.mapM_append]

def readbackValue (suite : String) (key : Origin → Origin) (initial : History F G) :
    Domain.Value (Structured.uniformCarriers F G) → Option (Value F G)
  | .transcript actual suffix =>
      if actual = suite then (readbackHistory key suffix).map fun history => .transcript (initial ++ history)
      else none
  | value => readbackData value

def readbackValues (suite : String) (key : Origin → Origin) (initial : History F G)
    (values : Domain.Environment (Structured.uniformCarriers F G)) : Option (List (Value F G)) :=
  values.mapM (readbackValue suite key initial)

def readbackOutcome (suite : String) (key : Origin → Origin) (initial : History F G) :
    PIR.Outcome (Domain.Environment (Structured.uniformCarriers F G)) → PIR.Outcome (List (Value F G))
  | .stopped reason => .stopped reason
  | .returned values =>
      match readbackValues suite key initial values with
      | some legacy => .returned legacy
      | none => .stopped .refused

section Handler
variable {m : Type → Type} [Monad m]

/-- Project a query before calling the existing oracle. Invalid requests and
unrepresentable suffixes refuse without making an oracle call. -/
def query (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F) (history : Domain.History (Structured.uniformCarriers F G)) :
    (origin : Origin) → m (PIR.Outcome (Domain.Raw (.challenge origin : Domain.Event (Structured.uniformCarriers F G))))
  | ⟨entry, event, some ⟨method, operands, .field field⟩⟩ =>
      if method = "draw" ∧ operands = [] then
        match readbackHistory key history with
        | none => pure (.stopped .refused)
        | some suffix => do
            let answer ← challenge (initial ++ suffix ++
              [.challenge (key ⟨entry, event, some ⟨method, operands, .field field⟩⟩)])
            pure (.returned answer)
      else pure (.stopped .refused)
  | _ => pure (.stopped .refused)

/-- Outcome/proof handler of the authoritative Process. Receives preserve a
malformed unread head. Observations have already changed the transcript value;
they consume no proof message. Interactive delivery has its separate handler. -/
def runK {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A → Proof F G →
    (A → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | .done value, proof, next => next value proof
  | .halt reason, proof, _ => pure (.stopped reason, proof)
  | .call (.receive ty _ _ _) continuation, proof, next =>
      match proof with
      | [] => pure (.stopped .refused, [])
      | payload :: unread =>
          match Value.decode ty (.data payload) with
          | some value => runK key initial challenge (continuation value) unread next
          | none => pure (.stopped .refused, proof)
  | .call (.query history origin) continuation, proof, next =>
      if Domain.drawRequest origin then do
        let answer ← query key initial challenge history origin
        match answer with
        | .returned value => runK key initial challenge (continuation value) proof next
        | .stopped reason => pure (.stopped reason, proof)
      else pure (.stopped .refused, proof)
  | .call (.localService ..) _, proof, _ => pure (.stopped .refused, proof)
  | .call (.send ..) continuation, proof, next |
    .call (.observe ..) continuation, proof, next |
    .call (.checkpoint ..) continuation, proof, next =>
      runK key initial challenge (continuation ()) proof next

def run {A : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A) (proof : Proof F G) :
    m (PIR.Outcome A × Proof F G) :=
  runK key initial challenge process proof fun value unread => pure (.returned value, unread)

/-- The adapter calls the existing challenge function at the mapped key. Its
outer monad can carry the existing cache, randomness and resource counters. -/
theorem query_draw (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (history : Domain.History (Structured.uniformCarriers F G))
    (entry : String) (event : List String) (field : String) (suffix : History F G)
    (mapped : readbackHistory key history = some suffix) :
    query key initial challenge history ⟨entry, event, some (.draw field)⟩ = (do
      let answer ← challenge (initial ++ suffix ++ [.challenge (key ⟨entry, event, some (.draw field)⟩)])
      pure (.returned answer)) := by
  simp only [query, Request.draw, and_self, ite_true, mapped]

theorem query_of_draw (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (history : Domain.History (Structured.uniformCarriers F G)) (origin : Origin) (field : String)
    (request : origin.request = some (.draw field)) (suffix : History F G)
    (mapped : readbackHistory key history = some suffix) :
    query key initial challenge history origin = (do
      let answer ← challenge (initial ++ suffix ++ [.challenge (key origin)])
      pure (.returned (show Domain.Raw (.challenge origin : Domain.Event (Structured.uniformCarriers F G)) from
        by simpa only [Domain.Raw, request, Request.draw] using answer))) := by
  cases origin with
  | mk entry event asked =>
      simp only at request
      subst asked
      exact query_draw key initial challenge history entry event field suffix mapped

theorem drawRequest_of_draw (origin : Origin) (field : String)
    (request : origin.request = some (.draw field)) : Domain.drawRequest origin = true := by
  cases origin with
  | mk entry event asked =>
      simp only at request
      subst asked
      rfl

/-- Mapping precedes the existing stateful oracle, so its exact cache, random
state and resource post-state are preserved. No independent nominal sampling
or cache is introduced. This equation also covers repeated/adaptive calls. -/
theorem query_state {S : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → StateT S m F)
    (history : Domain.History (Structured.uniformCarriers F G))
    (entry : String) (event : List String) (field : String) (suffix : History F G)
    (mapped : readbackHistory key history = some suffix) (state : S) :
    (query key initial challenge history ⟨entry, event, some (.draw field)⟩) state = (do
      let (answer, post) ← challenge
        (initial ++ suffix ++ [.challenge (key ⟨entry, event, some (.draw field)⟩)]) state
      pure (.returned answer, post)) := by
  exact congrArg (fun computation => computation state)
    (query_draw key initial challenge history entry event field suffix mapped)

def oracle (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F) :
    Domain.Oracle m (Structured.uniformCarriers F G) Unit
  | history, .challenge origin, _ => do
      let answer ← query key initial challenge history origin
      pure (answer, ())
  | _, _, _ => pure (.stopped .refused, ())

theorem runK_bind {A B R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (continuation : A → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) B)
    (proof : Proof F G) (next : B → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK key initial challenge (process.bind continuation) proof next =
      runK key initial challenge process proof
        (fun value unread => runK key initial challenge (continuation value) unread next) := by
  induction process generalizing proof with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              cases Value.decode ty (.data payload) <;> simp only [PIR.Process.bind, runK, ih]
      | send | observe | checkpoint => simpa only [PIR.Process.bind, runK] using ih () proof
      | localService => rfl
      | query history origin =>
          simp only [PIR.Process.bind, runK]
          split
          next =>
            congr 1
            funext answer
            cases answer with
            | stopped => rfl
            | returned value => exact ih value proof
          next => rfl

/-- Only actually yielded values impose a continuation obligation. Stops and
failed receives preserve their existing outcome and unread suffix. -/
theorem runK_congr_yields {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (property : A → Prop) (yields : PIR.Yields property process)
    (next next' : A → Proof F G → m (PIR.Outcome R × Proof F G))
    (agree : ∀ value unread, property value → next value unread = next' value unread)
    (proof : Proof F G) :
    runK key initial challenge process proof next = runK key initial challenge process proof next' := by
  induction process generalizing proof with
  | done value => exact agree value proof yields
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              simp only [runK]
              cases Value.decode ty (.data payload) with
              | none => rfl
              | some value => exact ih value (yields value) unread
      | send | observe | checkpoint => exact ih () (yields ()) proof
      | localService => rfl
      | query history origin =>
          simp only [runK]
          split
          next =>
            congr 1
            funext answer
            cases answer with
            | stopped => rfl
            | returned value => exact ih value (yields value) proof
          next => rfl

theorem runK_sequence {R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (first rest : Domain.View.Block (Structured.uniformCarriers F G))
    (env : Domain.Environment (Structured.uniformCarriers F G)) (proof : Proof F G)
    (next : Domain.Environment (Structured.uniformCarriers F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK key initial challenge (Domain.View.sequence first rest env) proof next =
      runK key initial challenge (first env) proof
        (fun value unread => runK key initial challenge (rest value) unread next) := by
  simp only [Domain.View.sequence, runK, runK_bind]

/-- Checkpoints are erased only for this outcome/unread-proof property. The
complete runtime and its physical frames remain available separately. -/
theorem runK_forgetCheckpoints {A R : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK key initial challenge (process.interpret Original.forgetCheckpoints) proof next =
      runK key initial challenge process proof next := by
  induction process generalizing proof with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              cases Value.decode ty (.data payload) <;>
                simp only [PIR.Process.interpret, Original.forgetCheckpoints, PIR.Process.bind, runK, ih]
      | send | observe | checkpoint =>
          simpa only [PIR.Process.interpret, Original.forgetCheckpoints, PIR.Process.bind, runK] using ih () proof
      | localService => rfl
      | query history origin =>
          simp only [PIR.Process.interpret, Original.forgetCheckpoints, PIR.Process.bind, runK]
          split
          next =>
            congr 1
            funext answer
            cases answer with
            | stopped => rfl
            | returned value => exact ih value proof
          next => rfl

/-- A complete actual participant, including entry/return sorts and every stop.
Only the return environment is projected; unread proof is retained verbatim. -/
def validate [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (program : Structured.Program) (context : Context) (artifact : Participant)
    (key : Origin → Origin) (challenge : History F G → m F)
    (inputs : Domain.Environment (Structured.uniformCarriers F G)) (initial : History F G)
    (proof : Proof F G) : m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  runK key initial challenge
    (Domain.participant (Structured.ringModel F G) program context artifact inputs) proof
    fun result unread => pure (readbackOutcome context.suite key initial (.returned result.values), unread)

end Handler

section Helpers
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A found helper is the identical closure over the exact admitted prefix.
This equation preserves failure and does not assume successful helper results. -/
theorem callHelper_embed (program : Structured.Program)
    (entry : Structured.HelperDefinition (Structured.assignment F G) Structured.closedInterface)
    (found : (program.payload.definitions.foldl
      (Structured.Evaluation.extendMeanings Structured.SiteObservations.closed) []).find?
        (fun item => item.helper.name == entry.helper.name) = some entry)
    (data : entry.helper.outputs.all dataType = true)
    {values : List (Value F G)} {encoded : Domain.Environment (Structured.uniformCarriers F G)}
    (ok : embedValues values = some encoded) :
    Domain.callHelper (Structured.ringModel F G) program entry.helper.name
        (entry.helper.outputs.map ValueSort.data) encoded =
      embedOutcome (callHelper
        (program.payload.definitions.foldl
          (Structured.Evaluation.extendMeanings Structured.SiteObservations.closed) [])
        entry.helper.name values) := by
  rw [Domain.callHelper, Domain.Binding.helperTable_ringModel, found]
  simp only [↓reduceIte, decodeValues_embed _ ok, callHelper, found]
  cases decoded : decodeValues entry.helper.inputs values with
  | none => rfl
  | some arguments =>
      simp only
      have closed : Domain.closedOutcome (entry.invoke arguments) = closedOutcome (entry.invoke arguments) :=
        by cases entry.invoke arguments <;> rfl
      rw [closed]
      cases outcome : closedOutcome (entry.invoke arguments) with
      | stopped reason => rfl
      | returned results =>
          simp only [embedOutcome, encodeValues_embed results data]
          cases Domain.encodeValues results <;> rfl

end Helpers
end Zkc.Construction.Uniform.DomainAdapter
