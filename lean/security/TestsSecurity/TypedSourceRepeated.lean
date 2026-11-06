module

public import TestsSecurity.TypedSourceExecution
public meta import TestsSecurity.TypedSourceExecution

@[expose] public section

/-! Exact executable controls for the retained repeated source. Its abstract
coordinate keys use opaque `Nat.repr` through `toString`, so these concrete
checks run the actual Process rather than asking kernel reflexivity to unfold
that representation. The generic all-reply reading remains kernel checked.
No source body or endpoint evaluator is reimplemented here. -/
set_option autoImplicit false
set_option maxRecDepth 20000
namespace TestsSecurity.TypedSourceRepeated
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir Tests.IndexServices TestsSecurity.TypedSourceExecution

/-- Reading includes the complete source result and reached frames/history for
all models, all raw replies and every stopped suffix of this actual source. -/
theorem reading (model : DomainModel) (state : Original.State model.toCarriers) :
    DomainReduction.Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.fold repeatedRouting
        (Occurrence.participant model Repeated.program 1 (repeatedInputs model)) state)
      (DomainSourceReading.presentation repeatedRouting
        (Occurrence.participant model Repeated.program 1 (repeatedInputs model)) state) :=
  DomainSourceReading.reading repeatedRouting
    (Repeated.context.replacement?.get (by decide +kernel)) (by kernel_rfl) rfl _ state

/-- Reject every unexpected event or nominal payload while inspecting this
fixture's full trace. All query origins and scalar messages are retained. -/
def inspect {carriers : Carriers} (events : Domain.History carriers) :
    Option (List (Origin × Option Nat)) :=
  events.mapM fun event => match event with
    | .challenge origin => some (origin, none)
    | .message origin payload => (payload.value .index).map fun value => (origin, some value)
    | .publicBinding _ => none

def queryOrigin (index : Nat) : Origin :=
  Domain.atCoordinates (Repeated.context.query "label_706f736974696f6e" (.sampleIndex 8)) [index]
def messageOrigin (index : Nat) : Origin :=
  Domain.atCoordinates (Repeated.context.message "label_64656c6976657279_0" 1 0) [index]
def expected : List (Origin × Option Nat) :=
  [(queryOrigin 0, none), (messageOrigin 0, some 0),
   (queryOrigin 1, none), (messageOrigin 1, some 0),
   (queryOrigin 2, none), (messageOrigin 2, some 0)]

def stoppedQuery (model : DomainModel) (history : Domain.History model.toCarriers)
    (event : Domain.Event model.toCarriers) :
    ExceptT PIR.Stop (StateM (List (Domain.History model.toCarriers))) (Domain.Raw event) :=
  ExceptT.mk fun log =>
    (if log.length = 1 then .error .reject else .ok (zeroReply model event),
      log ++ [history ++ [event]])

def stopSecond (model : DomainModel) : Domain.Oracle Id model.toCarriers Nat :=
  fun _ event count =>
    (if count = 1 then .stopped .reject else .returned (zeroReply model event), count + 1)

/-- The exact original output ABI is checked independently of execution. -/
theorem output_types : Repeated.program.payload.entry.outputs = [.boolean] := by kernel_rfl

def check : IO Unit := do
  let model := ringModel Int Int
  let result := repeated model
  unless result.2.length = 3 do throw (IO.userError "repeated source query count is not three")
  unless result.2.map List.length = [1, 3, 5] do
    throw (IO.userError "repeated source query prefixes changed")
  unless result.2.mapM inspect = some [expected.take 1, expected.take 3, expected.take 5] do
    throw (IO.userError "repeated source lost an exact origin, request, coordinate or message")
  match result.1.1 with
  | .stopped _ => throw (IO.userError "repeated source stopped")
  | .returned (values, state) =>
    unless state.frames = [] do throw (IO.userError "repeated source did not close its frames")
    unless inspect state.history = some expected do
      throw (IO.userError "repeated source final history changed")
    let values : Values (Component model.Value) [.boolean] := output_types ▸ values
    match values with
    | .cons (some true) .nil => pure ()
    | _ => throw (IO.userError "repeated source full result changed")
  unless result.1.2.isEmpty do throw (IO.userError "repeated source consumed or invented proof")
  unless result.2.length != (block model .validator).2.length do
    throw (IO.userError "repeated scalar queries were identified with one block query")
  -- The retained IndexServices route is deliberately query-only. It is not
  -- a complete source presentation until the actual delivery template is added.
  let queryOnly := (Zkc.Transcript.transform NominalDomain.interface (loggedQuery model)
    (DomainSourceReading.presentation Repeated.routing
      (Occurrence.participant model Repeated.program 1 (repeatedInputs model)) {}) [] []).run []
  unless queryOnly.2.mapM inspect = some [expected.take 1] do
    throw (IO.userError "query-only routing did not retain its exact first query")
  match queryOnly.1.1 with
  | .stopped .refused => pure ()
  | _ => throw (IO.userError "query-only routing did not refuse its missing delivery")
  let folded := Domain.run .validator (provider model)
    (Original.participant model Repeated.program repeatedRouting 1 (repeatedInputs model))
    ⟨[], [], 0⟩
  unless inspect folded.events = some expected && folded.state.oracle = 3 do
    throw (IO.userError "actual Original fold disagrees with nominal source trace")
  match folded.outcome with
  | .returned (_, state) =>
    unless state.frames = [] && inspect state.history = some expected do
      throw (IO.userError "actual Original fold returned wrong frames or history")
  | .stopped _ => throw (IO.userError "actual Original fold stopped")
  let stopped := (((Zkc.Transcript.transform NominalDomain.interface (stoppedQuery model)
    (DomainSourceReading.presentation repeatedRouting
      (Occurrence.participant model Repeated.program 1 (repeatedInputs model)) {}) [] []).run).run [])
  match stopped.1 with
  | .error .reject => pure ()
  | _ => throw (IO.userError "second provider stop was not preserved")
  unless stopped.2.mapM inspect = some [expected.take 1, expected.take 3] do
    throw (IO.userError "provider stop executed a delivery or suffix")
  let stoppedFold := Domain.run .validator (stopSecond model)
    (Original.participant model Repeated.program repeatedRouting 1 (repeatedInputs model))
    ⟨[], [], 0⟩
  match stoppedFold.outcome with
  | .stopped .reject => pure ()
  | _ => throw (IO.userError "actual Original fold lost second provider stop")
  unless inspect stoppedFold.events = some (expected.take 3) && stoppedFold.state.oracle = 2 do
    throw (IO.userError "actual Original fold lost attempted prefix or provider post-state")
  IO.println "PASS repeated actual source: three queries, exact [1,3,5] keys, six events, full result; missing-delivery refusal and second-query stop prefix"

#eval check
#print axioms reading

end TestsSecurity.TypedSourceRepeated
