import ZkcTools.StructuredSource.OpenEvaluation

/-! Focused abstract-transfer controls over explicit typed retained bodies.
These synthetic controls exercise the existing abstract analysis and observer;
they are not native correspondence or a general bound-soundness theorem. -/

set_option autoImplicit false

namespace Tests.StructuredApplicationBounds
open Lean Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource
open Bounds

private def checked (signature : ProtocolSignature)
    (body : Region protocolDialect signature.inputs signature.outputs) : CheckedProtocol where
  toProtocolSignature := signature
  raw := body.erase
  body := body
  formed := body.elaborate_erase

private def helper {inputs outputs : List Ty} (name : String) (kind : HelperKind)
    (body : Region dialect inputs outputs) : CheckedDefinition where
  name := name
  kind := kind
  inputs := inputs
  outputs := outputs
  raw := body.erase
  body := body
  formed := body.elaborate_erase

private def firstSignature : ProtocolSignature :=
  ⟨"First", ["A"], [.boolean, .boolean], [.boolean], [[0], [0]], [[0]]⟩
private def firstBody : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .ret (.cons .here .nil)
private def first : CheckedProtocol := checked firstSignature firstBody

private def constantSignature : ProtocolSignature :=
  ⟨"Constant", ["A"], [.boolean], [.boolean], [[0]], [[0]]⟩
private def constant : CheckedProtocol := checked constantSignature
  (.letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil)))

private def emptySignature : ProtocolSignature := ⟨"Empty", ["A"], [], [], [], []⟩
private def empty : CheckedProtocol := checked emptySignature (.ret .nil)

private def guardedSignature : ProtocolSignature :=
  ⟨"Guarded", ["A"], [.boolean], [], [[0]], []⟩
private def guarded : CheckedProtocol := checked guardedSignature
  (.letOp (.guard 0 "gate") (.cons .here .nil) .nil (.ret .nil))

private def strictHelper : CheckedDefinition := helper "strict" .local
  (.ret .nil : Region dialect [.boolean, .boolean] [])
private def strictSignature : ProtocolSignature :=
  ⟨"Strict", ["A"], [.boolean, .boolean], [], [[0], [0]], []⟩
private def strict : CheckedProtocol := checked strictSignature
  (.letOp (.localCall strictHelper.helper rfl 0 "strictCall")
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret .nil))

private def hugeHelper : CheckedDefinition := helper "huge" .local
  (.letOp (.indexConstant 0) .nil .nil
    (.letOp (.indexConstant (indexLimit - 1)) .nil .nil
      (.letOp (.loop [] []) (.cons (.there .here) (.cons .here .nil))
        (.cons (.ret .nil) .nil) (.ret .nil))) : Region dialect [] [])

private def vectorType : Ty := .vector scalarDomain
private def relaySignature : ProtocolSignature :=
  ⟨"Relay", ["A", "B"], [vectorType], [vectorType], [[0]], [[1]]⟩
private def relay : CheckedProtocol := checked relaySignature
  (.letOp (.exchange vectorType 0 1 "delivery") (.cons .here .nil) .nil
    (.letOp (.restrict vectorType [1]) (.cons .here .nil) .nil (.ret (.cons .here .nil))))
private def middleSignature : ProtocolSignature :=
  ⟨"Middle", ["X", "Y", "Z"], [vectorType], [vectorType], [[1]], [[0]]⟩
private def middle : CheckedProtocol := checked middleSignature
  (.letOp (.protocolApply relaySignature [1, 0] "inner") (.cons .here .nil) .nil
    (.ret (.cons .here .nil)))

private def noReplies (_ : Ty) : Analysis (Option Value) := pure none

private def call (definitions : List CheckedProtocol) (signature : ProtocolSignature)
    (roles : List Nat) (self : Nat) (args : Env)
    (received : Ty → Analysis (Option Value) := noReplies)
    (helpers : List CheckedDefinition := []) : Analysis Result := do
  let helpers ← prepareHelpers helpers
  let protocols ← prepareProtocols helpers definitions
  Bounds.protocolOperation helpers protocols {} self received
    (.protocolApply signature roles "outer") args .nil

private def suffix (signature : ProtocolSignature) (indices : List Nat) : RawRegion Ty ProtocolOp :=
  .letOp (.protocolApply signature [0] "child") indices signature.outputs .nil
    (.letOp (.localCall hugeHelper.helper rfl 0 "suffix") [] [] .nil (.ret []))

private def analyzeSuffix (definition : CheckedProtocol) (args : Env) : Analysis Result := do
  let helpers ← prepareHelpers [hugeHelper]
  let protocols ← prepareProtocols helpers [definition]
  Bounds.region (Bounds.protocolOperation helpers protocols {} 0 noReplies)
    (suffix definition.signature (List.range args.length)) args

private def arr (values : List Json) : Json := .arr values.toArray
private def receivedVector (size : Nat) (site : String := "unrelated") : ScriptReply :=
  ⟨arr [.str "receive", .str site, .str "sender", .str "receiver", wireType vectorType],
    arr [.str "value", arr (List.replicate size (.str "0"))]⟩
private def receivedBool (value : Bool) : ScriptReply :=
  ⟨arr [.str "receive", .str "bool", .str "sender", .str "receiver", wireType .boolean],
    arr [.str "value", .bool value]⟩

private def receiveCall (replies : List ScriptReply) : Analysis Result := do
  let envelope ← abstractReplies replies
  call [relay, middle] middleSignature [2, 0, 1] 2 [.vector (exact 7)] (receiveBounds envelope)

/-- Literal signature/raw equalities keep these controls independent of any
repeated checker reduction. Their typed bodies are hand-built test subjects. -/
theorem first_signature : first.signature = firstSignature := rfl
theorem first_raw : first.raw = firstBody.erase := rfl
theorem first_member : first ∈ [first, constant, empty, guarded] := by simp

/-- A complete original control unit, with forward source declaration order.
The candidate is normalized independently and admitted once in the kernel. -/
private def source : Snapshot :=
  (let contractDefinitions : List Definition := [
    .function ⟨"Main", .protocol, .publicDef, [.boolean, .boolean], [.boolean],
      some ⟨["A"], [["A"], ["A"]], [["A"]]⟩, [], some (.protocol ⟨"Main", []⟩),
      .block [.instruction (.protocolApply "First" ["A"]) [0, 1] [.boolean] [] "call"]
        (.ret [0])⟩,
    .function ⟨"First", .protocol, .publicDef, [.boolean, .boolean], [.boolean],
      some ⟨["A"], [["A"], ["A"]], [["A"]]⟩, [], some (.protocol ⟨"First", []⟩), .block [] (.ret [0])⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "Main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
private def mainSignature : ProtocolSignature :=
  ⟨"Main", ["A"], [.boolean, .boolean], [.boolean], [[0], [0]], [[0]]⟩
private def mainBody : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .letOp (.mark "call") .nil .nil
    (.letOp (.protocolApply firstSignature [0] "call")
      (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
private def mainDefinition : CheckedProtocol := checked mainSignature mainBody
set_option smartUnfolding false in
private theorem availability : checkUnitAvailability [] [first, mainDefinition] = .ok () := by
  rfl
private def unit : UnitPayload where
  definitions := []
  protocols := [first, mainDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := availability
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel
private def program : Program := ⟨source, unit⟩

set_option smartUnfolding false in
theorem kernel_admission : check source = .ok program := by rfl
private def imported : Imported source := ⟨program, kernel_admission⟩
theorem exact_subject : program.snapshot = source := imported.exactSubject
theorem main_signature : mainDefinition.signature = mainSignature := rfl
theorem main_raw : mainDefinition.raw = mainBody.erase := rfl
theorem main_member : mainDefinition ∈ unit.protocols := by simp [unit]
theorem source_first_member : first ∈ unit.protocols := List.mem_cons_self
theorem entry_selection : unit.entry = mainDefinition := rfl

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let result (name : String) (analysis : Analysis Result) (expected : Result) : IO Unit :=
    test name (match analysis.run {} with | .ok (actual, _) => actual == expected | _ => false)
  let failure {A : Type} (name : String) (analysis : Analysis A) (expected : Failure)
      (meter : Meter := {}) : IO Unit :=
    test name (match analysis.run meter with | .error actual => actual == expected | _ => false)

  result "missing unused protocol input remains absent without blocking projection"
    (call [first] firstSignature [0] 0 [.boolean (some true), .absent])
    (some [.boolean (some true)])
  result "optional input stays optional through the call"
    (call [first] firstSignature [0] 0 [.optional (.boolean (some true)), .absent])
    (some [.optional (.boolean (some true))])
  result "missing needed protocol input does not become an unknown present value"
    (call [first] firstSignature [0] 0 [.absent, .boolean (some true)]) (some [.absent])
  result "constant child can return with an absent unused input"
    (call [constant] constantSignature [0] 0 [.absent]) (some [.boolean (some true)])
  result "owned zero-result Local call still requires unused inputs"
    (call [strict] strictSignature [0] 0 [.boolean (some true), .absent]
      noReplies [strictHelper]) none
  result "optional Local inputs preserve the returning present path"
    (call [strict] strictSignature [0] 0 [.optional (.boolean (some true)), .boolean none]
      noReplies [strictHelper]) (some [])

  result "successful zero-result call is some empty tuple"
    (call [empty] emptySignature [0] 0 []) (some [])
  result "known false zero-result child has no return"
    (call [guarded] guardedSignature [0] 0 [.boolean (some false)]) none
  result "absent guard has no return"
    (call [guarded] guardedSignature [0] 0 [.absent]) none
  result "optional false guard has no returning path"
    (call [guarded] guardedSignature [0] 0 [.optional (.boolean (some false))]) none
  result "unknown guard preserves the true returning path"
    (call [guarded] guardedSignature [0] 0 [.boolean none]) (some [])
  result "known stop skips a costly caller suffix"
    (analyzeSuffix guarded [.boolean (some false)]) none
  failure "unknown guard keeps costly caller suffix reachable"
    (analyzeSuffix guarded [.boolean none]) .work
  failure "successful empty tuple continues to caller suffix" (analyzeSuffix empty []) .work
  result "outside zero-result call skips a known stop"
    (call [guarded] guardedSignature [2] 1 [.boolean (some false)]) (some [])
  result "outside call keeps full absent result ABI"
    (call [first] firstSignature [2] 1 [.boolean (some true), .boolean none]) (some [.absent])
  result "outside skip does not resolve the body"
    (call [] firstSignature [2] 1 [.absent, .absent]) (some [.absent])

  let mapped := ({} : ProtocolContext).enter "outer" [2, 0, 1] |>.enter "inner" [1, 0]
  result "nested mapped guard uses unchanged root self"
    (Bounds.protocolOperation {} [] mapped 0 noReplies (.guard 0 "gate")
      [.boolean (some false)] .nil) none
  result "nested unowned guard skips false condition"
    (Bounds.protocolOperation {} [] mapped 2 noReplies (.guard 0 "gate")
      [.boolean (some false)] .nil) (some [])
  result "nested draw owner uses unchanged root self"
    (Bounds.protocolOperation {} [] mapped 0 noReplies (.draw 0 scalarDomain "draw")
      [.absent] .nil) none
  result "nested unowned draw stays absent"
    (Bounds.protocolOperation {} [] mapped 2 noReplies (.draw 0 scalarDomain "draw")
      [.atom] .nil) (some [.absent])
  result "nested mapped Local owner strictly requires unused input"
    (do
      let helpers ← prepareHelpers [strictHelper]
      Bounds.protocolOperation helpers [] mapped 0 noReplies
        (.localCall strictHelper.helper rfl 0 "strictCall") [.boolean none, .absent] .nil) none
  result "nested unowned Local call skips a missing unused input"
    (Bounds.protocolOperation {} [] mapped 2 noReplies
      (.localCall strictHelper.helper rfl 0 "strictCall") [.boolean none, .absent] .nil) (some [])
  result "nested non-involutive mapping receives the independent vector"
    (call [relay, middle] middleSignature [2, 0, 1] 2 [.vector (exact 7)]
      (fun type => pure (if type == vectorType then some (.vector (exact 19)) else none)))
    (some [.vector (exact 19)])
  result "nested sender result is removed by mapped restriction and output mask"
    (call [relay, middle] middleSignature [2, 0, 1] 0 [.vector (exact 7)]) (some [.absent])
  result "proper-subset outsider never asks for a receive envelope"
    (call [relay, middle] middleSignature [2, 0, 1] 1 [.absent] (fun _ => throw .unknown))
    (some [.absent])
  result "receiver without a typed reply has no returning path"
    (call [relay, middle] middleSignature [2, 0, 1] 2 [.vector (exact 7)]) none

  let inputMasked := checked
    (ProtocolSignature.mk "Masked" ["A", "B"] [.boolean] [.boolean] [[0]] [[0, 1]])
    (.ret (.cons .here .nil))
  result "input mask removes an extra supplied unexposed value"
    (call [inputMasked] inputMasked.signature [1, 0] 0 [.boolean (some true)]) (some [.absent])
  let outputMasked := checked
    (ProtocolSignature.mk "OutputMasked" ["A", "B"] [] [.boolean] [] [[0]])
    (.letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil)))
  result "output mask removes constant result in the same closure"
    (call [outputMasked] outputMasked.signature [1, 0] 0 []) (some [.absent])
  let hiddenStop := checked
    (ProtocolSignature.mk "HiddenStop" ["A", "B"] [.boolean] [.boolean] [[0]] [[1]])
    (.letOp (.guard 0 "gate") (.cons .here .nil) .nil (.ret (.cons .here .nil)))
  result "hidden results do not erase an earlier stop"
    (call [hiddenStop] hiddenStop.signature [1, 0] 1 [.boolean (some false)]) none

  result "typed envelope joins every vector reply including unused suffix"
    (receiveCall [receivedVector 3 "first", receivedBool true, receivedVector 23 "last"])
    (some [.vector ⟨3, 23⟩])
  result "reply order and site do not guess a receive position"
    (receiveCall [receivedVector 23 "last", receivedBool false, receivedVector 3 "first"])
    (some [.vector ⟨3, 23⟩])
  result "wrong reply type never substitutes sender vector"
    (receiveCall [receivedBool true]) none
  let malformed : ScriptReply := ⟨(receivedVector 1).request, arr [.str "value", .bool true]⟩
  result "malformed reply does not erase valid unused suffix envelope"
    (receiveCall [malformed, receivedVector 11]) (some [.vector (exact 11)])
  result "oversized receive has no decoded returning envelope"
    (receiveCall [receivedVector 4097]) none
  failure "received vector is checked against the independent value limit"
    (call [relay] relaySignature [0, 1] 1 [.vector (exact 1)]
      (fun _ => pure (some (.vector (exact 4097))))) .value

  failure "missing inside table entry is refused"
    (call [] firstSignature [0] 0 [.absent, .absent]) .unknown
  for signature in [
      { firstSignature with roles := ["Renamed"] },
      { firstSignature with inputScopes := [[0, 1], [0]] },
      { firstSignature with outputScopes := [[0, 1]] },
      { firstSignature with inputs := [.index, .boolean] },
      { firstSignature with outputs := [.index] }] do
    failure "same name with different full signature is refused"
      (call [first] signature [0] 0 [.absent, .absent]) .unknown
  let publicSignature : ProtocolSignature :=
    ⟨"Public", ["A", "B"], [.boolean], [.boolean], [[0, 1]], [[0, 1]]⟩
  let publicDefinition := checked publicSignature (.ret (.cons .here .nil))
  for signature in [
      { publicSignature with roles := ["B", "A"] },
      { publicSignature with inputScopes := [[1, 0]] },
      { publicSignature with outputScopes := [[1, 0]] }] do
    failure "ordered roster and scope lists are exact signature fields"
      (call [publicDefinition] signature [0, 1] 0 [.boolean (some true)]) .unknown
  failure "wrong argument arity is refused before transfer"
    (call [first] firstSignature [0] 0 [.absent]) .unknown
  failure "wrong returned arity is refused after transfer"
    (invokeProtocolBound [⟨firstSignature, fun _ _ _ _ => pure (some [])⟩]
      firstSignature {} 0 noReplies [.absent, .absent]) .unknown
  failure "mask never silently truncates mismatched scope arity"
    (maskProtocolValues {} 0 [[0]] []) .unknown
  failure "duplicate protocol names never replace a captured closure"
    (prepareProtocols {} [first, first]) .unknown
  failure "an early closure cannot resolve a later definition"
    (call [middle, relay] middleSignature [2, 0, 1] 2 [.vector (exact 7)]
      (fun _ => pure (some (.vector (exact 19))))) .unknown

  let exhausted : Meter := { analysis := analysisLimit }
  failure "preparation entry checks analysis capacity before work"
    (prepareProtocols {} []) .analysis exhausted
  failure "lookup entry checks analysis capacity before work"
    (invokeProtocolBound [] emptySignature {} 0 noReplies []) .analysis exhausted
  failure "region entry checks analysis capacity before work"
    (Bounds.region (Bounds.protocolOperation {} [] {} 0 noReplies) (.ret []) []) .analysis exhausted
  failure "mask entry checks analysis capacity before allocation"
    (maskProtocolValues {} 0 [] []) .analysis exhausted
  failure "value union entry checks analysis capacity"
    ((Value.boolean none).join (.boolean (some true))) .analysis exhausted
  failure "empty receive envelope still checks analysis capacity"
    (receiveBounds [] vectorType) .analysis exhausted
  failure "empty reply scan still checks analysis capacity"
    (abstractReplies []) .analysis exhausted
  failure "protocol execution work has a separate limit"
    (call [empty] emptySignature [0] 0 []) .work { work := workLimit }
  let mut layered := [empty]
  let mut calleeName := emptySignature.name
  for i in List.range 18 do
    let callee : ProtocolSignature := ⟨calleeName, ["A"], [], [], [], []⟩
    let signature : ProtocolSignature := ⟨"Layer" ++ toString i, ["A"], [], [], [], []⟩
    let body : Region protocolDialect [] [] :=
      .letOp (.protocolApply callee [0] "left") .nil .nil
        (.letOp (.protocolApply callee [0] "right") .nil .nil (.ret .nil))
    layered := layered ++ [checked signature body]
    calleeName := signature.name
  failure "shared retained calls charge every occurrence before exponential expansion"
    (call layered ⟨calleeName, ["A"], [], [], [], []⟩ [0] 0 []) .analysis

  let request : OpenRequest := ⟨0, [.bool true, .null], [], 1⟩
  let inputs : OptionalValues [.boolean, .boolean] := .cons (some true) (.cons none .nil)
  test "one admitted source has the same preflight at different observer capacities"
    ((openPreflight unit request inputs).isOk &&
      (openPreflight unit { request with capacity := workLimit } inputs).isOk)
  let wireRequest (capacity : Nat) :=
    arr [.str "zkc.structured-open-request/0", .str "A", arr [.bool true, .null], arr [], toJson capacity]
  test "complete checked retained source returns with a missing unused input"
    (match evaluateOpen program (wireRequest 10) with
      | .ok actual => actual == arr [.str "zkc.structured-open-result/0",
          arr [.str "returned", arr [.bool true]], arr [], toJson (0 : Nat)]
      | _ => false)
  test "observer capacity remains a separate runtime refusal"
    (match evaluateOpen program (wireRequest 1) with
      | .error "structured-open-capacity" => true
      | _ => false)
  let receiveProcess : PIR.Process (observedInterface Scalar Scalar) (OptionalValues [vectorType]) :=
    .call (.action (.receive vectorType "unrelated" 0)) fun received =>
      .done (.cons (some received) .nil)
  test "oversized reply retains concrete observer value-limit refusal"
    (match observe ["sender", "receiver"] 1 2 receiveProcess
        { remaining := [receivedVector 4097] } with
      | .error "structured-open-value-limit" => true
      | _ => false)

  let failures ← failures.get
  unless failures.isEmpty do
    throw (IO.userError ("Structured application bounds failures:\n" ++
      String.intercalate "\n" failures.reverse))
  IO.println s!"Structured application bounds: {← count.get} controls passed"

#eval run

end Tests.StructuredApplicationBounds
