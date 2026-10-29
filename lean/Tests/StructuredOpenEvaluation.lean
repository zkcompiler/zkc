import ZkcTools.StructuredSource.OpenEvaluation

/-! Synthetic executable and kernel controls for scripted observation. These
subjects are hand-built; native-export comparisons belong to the parent bridge. -/

set_option autoImplicit false

namespace Tests.StructuredOpenEvaluation
open Lean Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource

private def arr (xs : List Json) : Json := .arr xs.toArray
private def strings (xs : List String) : Json := arr (xs.map Json.str)
private def roles : List String := ["P", "V"]
private def reply (request response : Json) : Json := arr [.str "reply", request, response]
private def value (v : Json) : Json := arr [.str "value", v]
private def unit : Json := strings ["unit"]
private def scriptStop (reason : String) : Json := strings ["stop", reason]
private def request (role : String) (inputs replies : List Json) (capacity : Nat := 1000000) : Json :=
  arr [.str "zkc.structured-open-request/0", .str role, arr inputs, arr replies, toJson capacity]
private def events (replies : List (Json × Json)) : List Json :=
  (replies.zipIdx).flatMap fun ((action, response), index) =>
    [arr [.str "request", toJson index, action], arr [.str "reply", toJson index, response]]
private def returned (values : List Json) (replies : List (Json × Json) := []) : Json :=
  arr [.str "zkc.structured-open-result/0", arr [.str "returned", arr values],
    arr (events replies), toJson replies.length]
private def stopped (reason site : String) (replies : List (Json × Json) := [])
    (pending : Option Json := none) : Json :=
  let position := replies.length
  let records := events replies ++
    pending.toList.map (fun action => arr [.str "request", toJson position, action]) ++
    [arr [.str "stop", .str reason, .str site, toJson position]]
  arr [.str "zkc.structured-open-result/0", strings ["stopped", reason, site],
    arr records, toJson position]
private def receiveBool : Json := arr [.str "receive", .str "delivery", .str "P", .str "V",
  wireType .boolean]
private def receiveProcess (localValue : Bool) :
    PIR.Process (observedInterface Scalar Scalar) (OptionalValues [.boolean]) :=
  ((Participant.exchange (services := services) (Value := OpenValue)
    1 0 1 "delivery" (some localValue)).interpret observeAction).bind fun result =>
      .done (.cons result .nil)

/-- Every receiver continuation uses the independent reply, for any local value. -/
theorem independent_receive (localValue : Bool) :
    receiveProcess localValue =
      .call (.action (.receive .boolean "delivery" 0))
        (fun received => .done (.cons (some received) .nil)) := by
  rfl

private def markedStop : PIR.Process (observedInterface Scalar Scalar) (OptionalValues []) :=
  .call (.mark "outer") fun _ => .call (.mark "inner.stop") fun _ => .halt .abort

/-- Trace serialization is executable; this equation checks the mark transition
in the kernel without assuming anything about its byte-counting implementation. -/
theorem marks_preserve_latest_site_without_replies (state : ReplayState) :
    observe roles 0 3 markedStop state =
      stopResult { state with site := "inner.stop" } .abort := by
  rfl

theorem exact_handle_request :
    actionRequest roles 0 (.query "draw.site" scalarDomain (.cons 29 .nil)) =
      .ok (strings ["draw", "draw.site", "P", scalarServiceContract, "29", scalarDomain]) := by
  rfl

theorem typed_receive_response :
    decodeActionValue (.receive .boolean "delivery" 0) (value (.bool true)) = .ok true := by
  rfl

theorem wrong_typed_response_refused :
    decodeActionValue (.receive .boolean "delivery" 0) unit =
      .error "structured-open-response" := by
  rfl

private def localStop (_ : Values OpenValue [.boolean]) :
    PIR.Process (observedInterface Scalar Scalar) (Values OpenValue []) :=
  .call (.mark "local.stop") fun _ => .halt .abort

theorem owned_zero_result_stop_keeps_mark (state : ReplayState) :
    observe roles 0 3
      (Participant.owned 0 0 localStop (.cons (some true) .nil)) state =
      stopResult { state with site := "local.stop" } .abort := by
  rfl

theorem owned_zero_result_missing_input_keeps_call_site (state : ReplayState) :
    observe roles 0 1
      (Participant.owned 0 0 localStop (.cons none .nil)) state =
      stopResult state .incomplete := by
  rfl

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def snapshot (defs : List Definition) : Snapshot := (let contractDefinitions : List Definition := defs
   ⟨digest, "main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩)
private def root (inputs outputs : List Ty) (inputScopes outputScopes : List (List String))
    (body : Block) : Definition :=
  .function ⟨"main", .protocol, .publicDef, inputs, outputs,
    some ⟨roles, inputScopes, outputScopes⟩, [], some (.protocol ⟨"main", []⟩), body⟩
private def localHelper (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .local, .privateDef, inputs, outputs, none, [], some (.local name []), body⟩
private def runSnapshot (source : Snapshot) (req : Json) : Except String Json := do
  evaluateOpen (← check source) req
private def expect (label : String) (actual : Except String Json) (expected : Json) : IO Unit := do
  match actual with
  | .error error => throw (IO.userError s!"{label}: refused {error}")
  | .ok actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {expected.compress}, got {actual.compress}")
private def refuse {A : Type} (label code : String) (actual : Except String A) : IO Unit := do
  match actual with
  | .error actual =>
    unless actual == code do throw (IO.userError s!"{label}: expected {code}, got {actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def boolExchange : Snapshot := snapshot [
  root [.boolean] [.boolean] [["P", "V"]] [["P", "V"]]
    (.block [.instruction (.exchange "P" "V") [0] [.boolean] [] "delivery"] (.ret [0]))]
private def sendBool : Json := arr [.str "send", .str "delivery", .str "P", .str "V",
  wireType .boolean, .bool false]
private def guardSource : Snapshot := snapshot [
  root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.guard "P") [0] [] [] "guard_site"] (.ret [0]))]
private def serviceSource (secondOwner : String := "P") : Snapshot := snapshot [
  root [.service scalarServiceContract, .service scalarServiceContract] [.field scalarDomain]
    [["P"], [secondOwner]] [["P"]]
    (.block [.instruction (.draw "P" scalarDomain) [0] [.field scalarDomain] [] "draw_site"]
      (.ret [0]))]
private def draw (handle : String) : Json :=
  strings ["draw", "draw_site", "P", scalarServiceContract, handle, scalarDomain]
private def twoDraws : Snapshot := snapshot [
  root [.service scalarServiceContract] [.field scalarDomain, .field scalarDomain]
    [["P"]] [["P"], ["P"]]
    (.block [
      .instruction (.draw "P" scalarDomain) [0] [.field scalarDomain] [] "draw_site",
      .instruction (.draw "P" scalarDomain) [1] [.field scalarDomain] [] "second_site"]
      (.ret [1, 0]))]
private def nestedLocal : Snapshot := snapshot [
  localHelper "stopper" [.boolean] [] (.block [] (.stop .abort "nested.stop")),
  localHelper "outer" [.boolean] []
    (.block [.instruction (.apply "stopper") [0] [] [] "inner.call"] (.ret [])),
  root [.boolean] [] [["P"]] []
    (.block [.instruction (.localCall "outer" "P") [0] [] [] "owner_call"] (.ret []))]
private def maskedAfterEffect : Snapshot := snapshot [
  root [.boolean] [.boolean] [["P"]] [["V"]]
    (.block [.instruction (.exchange "P" "V") [0] [.boolean] [] "delivery"] (.ret [0]))]
private def loopSource : Snapshot := snapshot [
  localHelper "loop" [.index, .index] []
    (.block [.instruction .loop [0, 1] []
      [.region [.index] [] (.block [] (.yield []))] "loop.site"] (.ret [])),
  root [.index, .index] [] [["P"], ["P"]] []
    (.block [.instruction (.localCall "loop" "P") [0, 1] [] [] "loop_call"] (.ret []))]
private def loopAfterReceive : Snapshot := snapshot [
  localHelper "loop" [.index, .index] []
    (.block [.instruction .loop [0, 1] []
      [.region [.index] [] (.block [] (.yield []))] "loop.site"] (.ret [])),
  root [.index, .index] [] [["P", "V"], ["P"]] []
    (.block [
      .instruction (.exchange "P" "V") [1] [.index] [] "bound",
      .instruction (.localCall "loop" "V") [1, 0] [] [] "loop_call"] (.ret []))]

def run : IO Unit := do
  let receiver := request "V" [.bool false] [reply receiveBool (value (.bool true))]
  expect "independent receive" (runSnapshot boolExchange receiver)
    (returned [.bool true] [(receiveBool, value (.bool true))])
  expect "send retains own value" (runSnapshot boolExchange
    (request "P" [.bool false] [reply sendBool unit]))
    (returned [.bool false] [(sendBool, unit)])
  expect "missing reply" (runSnapshot boolExchange (request "V" [.null] []))
    (stopped "incomplete" "delivery" [] (some receiveBool))
  expect "wrong order" (runSnapshot boolExchange
    (request "V" [.null] [reply sendBool unit, reply receiveBool (value (.bool true))]))
    (stopped "refused" "delivery" [] (some receiveBool))
  expect "wrong typed value" (runSnapshot boolExchange
    (request "V" [.null] [reply receiveBool (value (.str "1"))]))
    (stopped "refused" "delivery" [] (some receiveBool))
  expect "oversized response is an unconsumed mismatch" (runSnapshot boolExchange
    (request "V" [.null] [reply receiveBool (arr (List.replicate 4097 .null))]))
    (stopped "refused" "delivery" [] (some receiveBool))
  expect "wrong send response" (runSnapshot boolExchange
    (request "P" [.bool false] [reply sendBool (value (.bool true))]))
    (stopped "refused" "delivery" [] (some sendBool))
  expect "unused suffix" (runSnapshot boolExchange
    (request "V" [.null] [reply receiveBool (value (.bool true)), reply sendBool unit]))
    (returned [.bool true] [(receiveBool, value (.bool true))])
  for reason in ["abort", "reject", "exhausted", "incomplete", "refused"] do
    expect ("scripted stop " ++ reason) (runSnapshot boolExchange
      (request "V" [.null] [reply receiveBool (scriptStop reason)]))
      (stopped reason "delivery" [(receiveBool, scriptStop reason)])
  expect "invalid stop" (runSnapshot boolExchange
    (request "V" [.null] [reply receiveBool (scriptStop "unknown")]))
    (stopped "refused" "delivery" [] (some receiveBool))
  expect "guard site" (runSnapshot guardSource (request "P" [.bool false] []))
    (stopped "reject" "guard_site")
  expect "missing guard" (runSnapshot guardSource (request "P" [.null] []))
    (stopped "incomplete" "guard_site")
  expect "unowned guard" (runSnapshot guardSource (request "V" [.bool false] []))
    (returned [.null])
  expect "nested zero-result local stop" (runSnapshot nestedLocal (request "P" [.bool true] []))
    (stopped "abort" "nested.stop")
  expect "missing zero-result local input" (runSnapshot nestedLocal (request "P" [.null] []))
    (stopped "incomplete" "owner_call")
  expect "unowned zero-result local" (runSnapshot nestedLocal (request "V" [.bool true] []))
    (returned [])
  expect "output mask after send" (runSnapshot maskedAfterEffect
    (request "P" [.bool false] [reply sendBool unit]))
    (returned [.null] [(sendBool, unit)])
  expect "masked output preserves missing reply" (runSnapshot maskedAfterEffect
    (request "P" [.bool false] [])) (stopped "incomplete" "delivery" [] (some sendBool))
  for handle in ["17", "29", "18446744073709551615"] do
    let action := draw handle
    expect ("actual handle " ++ handle) (runSnapshot serviceSource
      (request "P" [.str handle, .str handle] [reply action (value (.str "8"))]))
      (returned [.str "8"] [(action, value (.str "8"))])
  expect "missing draw argument" (runSnapshot serviceSource (request "P" [.null, .null] []))
    (stopped "incomplete" "draw_site")
  expect "unowned draw" (runSnapshot serviceSource (request "V" [.null, .null] []))
    (returned [.null])
  let first := draw "17"
  let second := strings ["draw", "second_site", "P", scalarServiceContract, "17", scalarDomain]
  let consumed := [(first, value (.str "3"))]
  expect "missing second reply retains consumed prefix" (runSnapshot twoDraws
    (request "P" [.str "17"] [reply first (value (.str "3"))]))
    (stopped "incomplete" "second_site" consumed (some second))
  expect "second request mismatch is unconsumed" (runSnapshot twoDraws
    (request "P" [.str "17"]
      [reply first (value (.str "3")), reply first (value (.str "8"))]))
    (stopped "refused" "second_site" consumed (some second))
  expect "two independent service replies" (runSnapshot twoDraws
    (request "P" [.str "17"]
      [reply first (value (.str "3")), reply second (value (.str "8"))]))
    (returned [.str "3", .str "8"] (consumed ++ [(second, value (.str "8"))]))
  refuse "cross-owner alias" "structured-service-alias" (runSnapshot (serviceSource "V")
    (request "P" [.str "17", .str "17"] []))
  refuse "unowned handle out of range" "structured-input-natural-range" (runSnapshot serviceSource
    (request "V" [.str "18446744073709551616", .null] []))
  refuse "role exact spelling" "structured-open-role"
    (runSnapshot guardSource (request "p" [.bool true] []))
  refuse "request exact arity" "structured-open-request"
    (runSnapshot guardSource (arr [.str "zkc.structured-open-request/0"]))
  refuse "input exact arity" "structured-input-count"
    (runSnapshot guardSource (request "P" [] []))
  refuse "capacity zero" "structured-open-capacity"
    (runSnapshot guardSource (request "P" [.bool true] [] 0))
  refuse "capacity too large" "structured-number-limit"
    (runSnapshot guardSource (request "P" [.bool true] [] 1000001))
  refuse "observer exhaustion" "structured-open-capacity"
    (runSnapshot guardSource (request "P" [.bool true] [] 1))
  refuse "invalid unused reply envelope" "structured-open-reply" (runSnapshot guardSource
    (request "P" [.bool true] [strings ["bad"]]))
  refuse "too many replies" "structured-list-limit" (runSnapshot guardSource
    (request "P" [.bool true] (List.replicate 4097 (reply sendBool unit))))
  expect "small local loop" (runSnapshot loopSource (request "P" [.str "0", .str "2"] []))
    (returned [])
  refuse "large local loop preflight" "structured-open-work-limit" (runSnapshot loopSource
    (request "P" [.str "0", .str "18446744073709551615"] []))
  let receiveIndex := arr [.str "receive", .str "bound", .str "P", .str "V", wireType .index]
  refuse "large received loop bound" "structured-open-work-limit" (runSnapshot loopAfterReceive
    (request "V" [.str "0", .null]
      [reply receiveIndex (value (.str "18446744073709551615"))]))
  for bad in ["", "00", "01", "-1", "+1", " 1", "1.0", "1e0", toString scalarModulus] do
    if (wireInput (.field scalarDomain) (.str bad)).isOk then
      throw (IO.userError ("noncanonical field accepted: " ++ bad))
  if (wireInput (.vector scalarDomain) (arr (List.replicate 4097 (.str "0")))).isOk then
    throw (IO.userError "oversized vector accepted")
  let vectorSource := snapshot [root [.vector scalarDomain] [.vector scalarDomain]
    [["P"]] [["V"]] (.block [
      .instruction (.exchange "P" "V") [0] [.vector scalarDomain] [] "vector_delivery"] (.ret [0]))]
  let vectorRequest := arr [.str "receive", .str "vector_delivery", .str "P", .str "V",
    wireType (.vector scalarDomain)]
  let vectorBoundary := arr (List.replicate 4096 (.str "0"))
  expect "received vector capacity boundary" (runSnapshot vectorSource
    (request "V" [.null] [reply vectorRequest (value vectorBoundary)]))
    (returned [vectorBoundary] [(vectorRequest, value vectorBoundary)])
  refuse "received vector capacity is observer refusal" "structured-open-value-limit"
    (runSnapshot vectorSource (request "V" [.null]
      [reply vectorRequest (value (arr (List.replicate 4097 (.str "0"))))]))
  expect "malformed vector value remains semantic refusal" (runSnapshot vectorSource
    (request "V" [.null] [reply vectorRequest (value (arr [.bool false]))]))
    (stopped "refused" "vector_delivery" [] (some vectorRequest))
  expect "oversized malformed reply shape remains semantic refusal" (runSnapshot vectorSource
    (request "V" [.null] [reply vectorRequest (arr (List.replicate 513 (.str "value")))]))
    (stopped "refused" "vector_delivery" [] (some vectorRequest))
  let groupRoot := snapshot [root [.group groupDomain] [.group groupDomain]
    [["P"]] [["P"]] (.block [] (.ret [0]))]
  expect "additive group wire value" (runSnapshot groupRoot (request "P" [.str "7"] []))
    (returned [.str "7"])
  refuse "malformed closed group input" "structured-input-type"
    (input (.group groupDomain) (arr []))
  refuse "closed service output" "structured-open-profile" (output (.service scalarServiceContract) 17)
  refuse "service owner invariant" "structured-service-owner"
    (validateServiceAliases [[]]
      (.cons (ty := .service scalarServiceContract) (some 17) .nil) [])
  refuse "trace byte capacity" "structured-open-record-limit"
    (stopResult { remaining := [], recordBytes := 1024 * 1024 } .abort)
  let closed := snapshot [.function ⟨"main", .protocol, .publicDef,
    [.boolean], [.boolean], some ⟨["P"], [["P"]], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [] (.ret [0])⟩]
  expect "legacy closed output" (do
    evaluate (← check closed) (arr [arr [.str "bool", .bool true]]))
    (arr [.str "returned", arr [arr [.str "bool", .bool true]]])
  let closedGroup := snapshot [.function ⟨"main", .protocol, .publicDef,
    [.group groupDomain], [.group groupDomain], some ⟨["P"], [["P"]], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [] (.ret [0])⟩]
  expect "closed explicit additive group" (do
    evaluate (← check closedGroup) (arr [arr [.str "group", .str groupDomain, .str "7"]]))
    (arr [.str "returned", arr [arr [.str "group", .str groupDomain, .str "7"]]])
  refuse "closed group domain" "structured-input-domain"
    (input (.group groupDomain) (arr [.str "group", .str scalarDomain, .str "7"]))
  let padded := "[]" ++ String.ofList (List.replicate (1024 * 1024) ' ')
  unless (Structured.Format.parse padded).isOk do
    throw (IO.userError "source parser did not accept above the request byte limit")
  if (Structured.Format.parse padded (1024 * 1024)).isOk then
    throw (IO.userError "request parser exceeded the request byte limit")
  if (Structured.Format.parse (String.ofList (List.replicate 65 '['))).isOk then
    throw (IO.userError "request parser exceeded the depth limit")
  IO.println "Structured open evaluation controls passed"

#eval run

end Tests.StructuredOpenEvaluation
