module

public import ZkcTools.StructuredSource.OpenValues

@[expose] public section

/-! Bounded scripted observation of the admitted open process. This executable
capacity counts visited Process constructors, including marks and the terminal
constructor. It is not the native reference's SSA work count. -/

namespace ZkcTools.StructuredSource
open Lean Zkc.Source Zkc.Source.Structured

abbrev OpenAction := Participant.Action Nat Ty services OpenValue

structure ScriptReply where
  request : Json
  response : Json

structure OpenRequest where
  self : Nat
  inputs : List Json
  replies : List ScriptReply
  capacity : Nat

def decodeScriptReply (json : Json) : Except String ScriptReply := do
  let [.str "reply", request, response] ← Structured.Format.array json | throw "structured-open-reply"
  let .arr _ := request | throw "structured-open-reply"
  let .arr _ := response | throw "structured-open-reply"
  return ⟨request, response⟩

def decodeOpenRequest (roles : List String) (json : Json) : Except String OpenRequest := do
  let [.str "zkc.structured-open-request/0", .str role, values, replies, capacity] ←
    Structured.Format.array json | throw "structured-open-request"
  let some self := roles.idxOf? role | throw "structured-open-role"
  let capacity ← Format.natural capacity workLimit
  if capacity == 0 then throw "structured-open-capacity"
  return ⟨self, ← Structured.Format.array values, ← (← Structured.Format.array replies 4096).mapM decodeScriptReply,
    capacity⟩

def actionRequest (roles : List String) (self : Nat) : OpenAction → Except String Json
  | .send (ty := type) site receiver value => do
    if type.isHandle then throw "structured-open-message-handle"
    return .arr #[.str "send", .str site, .str (roles[self]?.getD ""),
      .str (roles[receiver]?.getD ""), wireType type, ← wireOutput type value]
  | .receive type site sender => do
    if type.isHandle then throw "structured-open-message-handle"
    return .arr #[.str "receive", .str site, .str (roles[sender]?.getD ""),
      .str (roles[self]?.getD ""), wireType type]
  | .query site field (.cons handle .nil) =>
    return .arr #[.str "draw", .str site, .str (roles[self]?.getD ""),
      .str ("random." ++ (show String from field) ++ "/0"), .str (toString handle), .str field]

def actionSite : OpenAction → String
  | .send site .. | .receive _ site .. | .query site .. => site

def decodeActionValue : (action : OpenAction) → Json →
    Except String ((participantInterface Scalar Scalar).Reply action)
  | .send .., json => do
    let [.str "unit"] ← Structured.Format.array json | throw "structured-open-response"
    return ()
  | .receive type .., json => do
    let [.str "value", value] ← Structured.Format.array json | throw "structured-open-response"
    match wireInput type value with
    | .error "structured-list-limit" => throw "structured-open-value-limit"
    | result => result
  | .query _ field _, json => do
    let [.str "value", value] ← Structured.Format.array json | throw "structured-open-response"
    wireInput (.field field) value

structure ReplayState where
  remaining : List ScriptReply
  position : Nat := 0
  site : String := ""
  records : Array Json := #[]
  recordBytes : Nat := 2

/-- Count compact UTF-8 record bytes before extending the trace. As in the
reference, one separator byte is charged for each record, including the first. -/
def record (state : ReplayState) (event : Json) : Except String ReplayState := do
  let bytes := state.recordBytes + event.compress.utf8ByteSize + 1
  if bytes > 1024 * 1024 then throw "structured-open-record-limit"
  return { state with records := state.records.push event, recordBytes := bytes }

def stopResult (state : ReplayState) (reason : PIR.Stop) : Except String Json := do
  let reason := Zkc.Source.Format.stop.encode reason
  let state ← record state (.arr #[.str "stop", reason, .str state.site, toJson state.position])
  return .arr #[.str "zkc.structured-open-result/0",
    .arr #[.str "stopped", reason, .str state.site], .arr state.records, toJson state.position]

def returnedResult {types : List Ty} (state : ReplayState) (values : OptionalValues types) :
    Except String Json := do
  return .arr #[.str "zkc.structured-open-result/0",
    .arr #[.str "returned", .arr (← optionalOutputs values).toArray],
    .arr state.records, toJson state.position]

/-- Only a matching request and a well-typed value/unit or valid stop consumes a
reply. Malformed responses produce refused without consuming their position. -/
def replay (roles : List String) (self : Nat) (action : OpenAction) (state : ReplayState) :
    Except String (PIR.Outcome ((participantInterface Scalar Scalar).Reply action) × ReplayState) := do
  let request ← actionRequest roles self action
  let state ← record { state with site := actionSite action }
    (.arr #[.str "request", toJson state.position, request])
  let reply :: remaining := state.remaining | return (.stopped .incomplete, state)
  if reply.request != request then return (.stopped .refused, state)
  let result : PIR.Outcome ((participantInterface Scalar Scalar).Reply action) ←
    match Structured.Format.array reply.response with
    | .ok [.str "stop", reason] =>
      match Zkc.Source.Format.stop.decode reason with
      | .ok reason => pure (.stopped reason)
      | .error _ => return (.stopped .refused, state)
    | _ =>
      match decodeActionValue action reply.response with
      | .ok value => pure (.returned value)
      | .error "structured-open-value-limit" => throw "structured-open-value-limit"
      | .error _ => return (.stopped .refused, state)
  let state ← record state (.arr #[.str "reply", toJson state.position, reply.response])
  return (result, { state with remaining, position := state.position + 1 })

/-- Capacity is an observer resource refusal, never a semantic `exhausted` stop.
An internal mark is handled locally and cannot consume a provider reply. -/
def observe {types : List Ty} (roles : List String) (self : Nat) : Nat →
    PIR.Process (observedInterface Scalar Scalar) (OptionalValues types) →
    ReplayState → Except String Json
  | 0, _, _ => .error "structured-open-capacity"
  | _ + 1, .done values, state => returnedResult state values
  | _ + 1, .halt reason, state => stopResult state reason
  | fuel + 1, .call (.mark site) next, state =>
    observe roles self fuel (next ()) { state with site }
  | fuel + 1, .call (.action action) next, state => do
    let (result, state) ← replay roles self action state
    match result with
    | .stopped reason => stopResult state reason
    | .returned value => observe roles self fuel (next value) state

/-- Decode only well-typed receive values for the abstract envelope. Every
supplied reply is inspected, including unused suffixes. Malformed replies still
have their original replay behavior; none can resume with an unbounded value. -/
def abstractReplies (replies : List ScriptReply) : Bounds.Analysis (List (Ty × Bounds.Value)) := do
  Bounds.tick
  let mut result := []
  for reply in replies do
    -- Charge scanning even malformed/unused envelopes, independently of runtime work.
    Bounds.tick
    Bounds.tick (1 + reply.request.compress.utf8ByteSize + reply.response.compress.utf8ByteSize)
    match Structured.Format.array reply.request, Structured.Format.array reply.response with
    | .ok [.str "receive", _, _, _, type], .ok [.str "value", value] =>
      match Format.type type with
      | .error _ => pure ()
      | .ok type => match wireInput type value with
        | .error _ => pure ()
        | .ok value =>
          let bound := Bounds.value type value
          Bounds.checkValue bound
          result := (type, bound) :: result
    | _, _ => pure ()
  return result

/-- Bounds are per type and include all typed replies, not a guessed script
position. Without any typed reply, this receive cannot resume; replay still
reports its own missing/mismatched response or oversized-value error. -/
def receiveBounds (replies : List (Ty × Bounds.Value)) (type : Ty) : Bounds.Analysis (Option Bounds.Value) := do
  Bounds.tick
  let mut bound := none
  for (actual, value) in replies do
    Bounds.tick
    if actual == type then
      bound := some (← match bound with
        | none => pure value
        | some previous => previous.join value)
  return bound

def optionalAbstractInputs {types : List Ty} : OptionalValues types → Bounds.Env
  | .nil => []
  | .cons (ty := type) value rest =>
    (value.elim .absent (Bounds.value type)) :: optionalAbstractInputs rest

/-- Preflight runs before process construction, including eager ranges inside
Local callbacks and retained protocol repeats. Repeat callbacks keep their
optional captures, root context and preceding protocol table. Unknown branches,
loop prefixes (even before a definite stop) and all typed replies remain
conservative; capacity failures do not become semantic stops. -/
def openPreflight (payload : UnitPayload) (request : OpenRequest)
    (values : OptionalValues payload.entry.inputs) : Except String Unit := do
  let analysis : Bounds.Analysis Unit := do
    let helpers ← Bounds.prepareHelpers payload.definitions
    let protocols ← Bounds.prepareProtocols helpers payload.protocols
    let replies ← abstractReplies request.replies
    let inputs := optionalAbstractInputs values
    inputs.forM Bounds.checkValue
    let result ← Bounds.invokeProtocolBound protocols payload.entry.signature {} request.self
      (receiveBounds replies) inputs
    if let some outputs := result then outputs.forM Bounds.outputWork
    return ()
  let _ ← (analysis.run {}).mapError (Bounds.Failure.code true)
  return ()

def evaluateOpen (program : Program) (json : Json) : Except String Json := do
  let root := program.payload.entry
  let request ← decodeOpenRequest root.roles json
  let values ← optionalInputs root.inputs request.inputs
  validateServiceAliases root.inputScopes values []
  openPreflight program.payload request values
  observe root.roles request.self request.capacity
    (program.observed Scalar Scalar request.self values) { remaining := request.replies }

end ZkcTools.StructuredSource
