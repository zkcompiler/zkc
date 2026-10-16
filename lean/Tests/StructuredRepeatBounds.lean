import ZkcTools.StructuredSource.OpenEvaluation

/-! Retained-repeat abstract transfer and open-observer controls. Raw subjects
isolate conservative preflight behavior; complete synthetic snapshots also use
the existing checker and process. These are not a soundness or CPU-cost proof. -/

set_option autoImplicit false

namespace Tests.StructuredRepeatBounds
open Lean Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource
open Bounds

private def vectorType : Ty := .vector scalarDomain
private def fieldType : Ty := .field scalarDomain
private def noReplies (_ : Ty) : Analysis (Option Value) := pure none
private def callback (spec : RepeatSpec) (body : RawRegion Ty ProtocolOp) :
    RawRegions Ty ProtocolOp :=
  .cons (.index :: (spec.state ++ spec.captures)) spec.state body .nil
private def transfer (spec : RepeatSpec) (body : RawRegion Ty ProtocolOp) (args : Env)
    (context : ProtocolContext := {}) (self : Nat := 0)
    (received : Ty → Analysis (Option Value) := noReplies)
    (protocols : ProtocolBounds := []) (helpers : Helpers := {}) : Analysis Result :=
  Bounds.protocolOperation helpers protocols context self received (.repeat spec "repeat")
    args (callback spec body)
private def repeatRegion (spec : RepeatSpec) (body : RawRegion Ty ProtocolOp)
    (indices : List Nat) (next : RawRegion Ty ProtocolOp) : RawRegion Ty ProtocolOp :=
  .letOp (.repeat spec "repeat") indices spec.state (callback spec body) next
private def analyze (body : RawRegion Ty ProtocolOp) (args : Env)
    (helpers : Helpers := {}) : Analysis Result :=
  Bounds.region (Bounds.protocolOperation helpers [] {} 0 noReplies) body args

private def booleanSpec : RepeatSpec := ⟨[.boolean], [.boolean], [0], [[0]], 3⟩
private def emptySpec : RepeatSpec := ⟨[], [], [0], [], 3⟩
private def vectorSpec : RepeatSpec := ⟨[vectorType], [fieldType], [0], [[0]], 3⟩
private def helper {inputs outputs : List Ty} (name : String)
    (body : Region dialect inputs outputs) : CheckedDefinition where
  name := name
  kind := .local
  inputs := inputs
  outputs := outputs
  raw := body.erase
  body := body
  formed := body.elaborate_erase
private def appendHelper : CheckedDefinition := helper "Append"
  (.letOp (.exec (.vectorAppend scalarDomain))
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)) :
    Region dialect [vectorType, fieldType] [vectorType])
private def hugeHelper : CheckedDefinition := helper "Huge"
  (.letOp (.indexConstant 0) .nil .nil
    (.letOp (.indexConstant (indexLimit - 1)) .nil .nil
      (.letOp (.loop [] []) (.cons (.there .here) (.cons .here .nil))
        (.cons (.ret .nil) .nil) (.ret .nil))) : Region dialect [] [])
private def appendBody : RawRegion Ty ProtocolOp :=
  .letOp (.localCall appendHelper.helper rfl 0 "append") [1, 2] [vectorType] .nil (.ret [0])
private def hugeBody : RawRegion Ty ProtocolOp :=
  .letOp (.localCall hugeHelper.helper rfl 0 "huge") [] [] .nil (.ret [])
private def checked (signature : ProtocolSignature)
    (body : Region protocolDialect signature.inputs signature.outputs) : CheckedProtocol where
  toProtocolSignature := signature
  raw := body.erase
  body := body
  formed := body.elaborate_erase
private def relaySignature : ProtocolSignature :=
  ⟨"Relay", ["Sender", "Receiver"], [vectorType], [vectorType], [[0]], [[1]]⟩
private def relay : CheckedProtocol := checked relaySignature
  (.letOp (.exchange vectorType 0 1 "delivery") (.cons .here .nil) .nil
    (.ret (.cons .here .nil)))
private def mappedSpec : RepeatSpec := ⟨[vectorType], [], [0, 1], [[0]], 2⟩
private def mappedBody : Region protocolDialect [.index, vectorType] [vectorType] :=
  .letOp (.protocolApply relaySignature [1, 0] "inner")
    (.cons (.there .here) .nil) .nil (.ret (.cons .here .nil))
private def mappedSignature : ProtocolSignature :=
  ⟨"Mapped", ["A", "B", "C"], [.index, vectorType], [vectorType], [[0, 1], [1]], [[0]]⟩
private def mapped : CheckedProtocol := checked mappedSignature
  (.letOp (.repeat mappedSpec "repeat") (.cons .here (.cons (.there .here) .nil))
    (.cons mappedBody .nil) (.ret (.cons .here .nil)))

private def arr (values : List Json) : Json := .arr values.toArray
private def wireRequest (role : String) (inputs : List Json) (replies : List Json := [])
    (capacity : Nat := workLimit) : Json :=
  arr [.str "zkc.structured-open-request/0", .str role, arr inputs, arr replies, toJson capacity]
private def source (maximum : Nat) : Snapshot :=
  (let contractDefinitions : List Definition := [
    .function ⟨"Main", .protocol, .publicDef, [.index, .boolean, .boolean], [.boolean],
      some ⟨["P", "Q"], [["P"], ["P"], ["P"]], [["P"]]⟩, [], none,
      .block [.instruction (.protocolRepeat 1 maximum ["P"] [["P"]])
        [0, 1, 2] [.boolean]
        [.region [.index, .boolean, .boolean] [.boolean]
          (.block [.instruction (.guard "P") [2] [] [] "gate"] (.yield [1]))]
        "repeat"] (.ret [0])⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "Main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none)⟩)
private def runSource (maximum : Nat) (request : Json) : Except String Json := do
  evaluateOpen (← check (source maximum)) request
private def returned (values : List Json) : Json :=
  arr [.str "zkc.structured-open-result/0", arr [.str "returned", arr values], arr [], toJson (0 : Nat)]
private def stopped (reason site : String) : Json :=
  arr [.str "zkc.structured-open-result/0", arr [.str "stopped", .str reason, .str site],
    arr [arr [.str "stop", .str reason, .str site, toJson (0 : Nat)]], toJson (0 : Nat)]
private def receivedVector (size : Nat) : ScriptReply :=
  ⟨arr [.str "receive", .str "unrelated", .str "P", .str "Q", wireType vectorType],
    arr [.str "value", arr (List.replicate size (.str "0"))]⟩

private def serviceSource : Snapshot :=
  (let contractDefinitions : List Definition := [
    .function ⟨"Main", .protocol, .publicDef, [.index, .service scalarServiceContract], [],
      some ⟨["P", "Q"], [["P"], ["P"]], []⟩, [], none,
      .block [
        .instruction (.draw "P" scalarDomain) [1] [fieldType] [] "prelude",
        .instruction (.protocolRepeat 0 3 ["P"] []) [1, 2] []
          [.region [.index, .service scalarServiceContract] []
            (.block [.instruction (.draw "P" scalarDomain) [1] [fieldType] [] "draw"]
              (.yield []))] "repeat",
        .instruction (.draw "P" scalarDomain) [2] [fieldType] [] "suffix"] (.ret [])⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "Main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none)⟩)
private def drawRequest (site : String) : Json :=
  arr [.str "draw", .str site, .str "P", .str scalarServiceContract, .str "7", .str scalarDomain]
private def drawReply (site : String) (response : Json) : Json :=
  arr [.str "reply", drawRequest site, response]
private def traceRecords (replies : List (String × Json)) : List Json :=
  replies.zipIdx.flatMap fun ((site, response), position) =>
    [arr [.str "request", toJson position, drawRequest site],
      arr [.str "reply", toJson position, response]]
private def runService (n : Nat) (replies : List (String × Json)) : Except String Json := do
  evaluateOpen (← check serviceSource)
    (wireRequest "P" [.str (toString n), .str "7"]
      (replies.map fun (site, response) => drawReply site response))

/-- The existing zero-step transfer does not demand its callback. -/
theorem iterate_zero (step : Nat → Env → Analysis Result) (index : Nat) (state : Env) :
    iterate step 0 index state = pure state := rfl

/-- A stopping abstract callback preserves the prior prefix, including empty
state. This is an analysis equation, not a returning-process theorem. -/
theorem stopped_iteration_prefix (index : Nat) (state : Env) :
    iterate (fun _ _ => pure none) 1 index state = (do visit; pure state) := by
  rfl

theorem no_return_join_empty :
    joinResult none (some []) = (pure (some []) : Analysis Result) := rfl

/-- Typed callback storage uses the same retained Region as ordinary protocols. -/
theorem mapped_callback_raw : mapped.raw =
    (Region.letOp (.repeat mappedSpec "repeat")
      (.cons .here (.cons (.there .here) .nil)) (.cons mappedBody .nil)
      (.ret (.cons .here .nil)) :
        Region protocolDialect [.index, vectorType] [vectorType]).erase := rfl

#print axioms iterate_zero
#print axioms stopped_iteration_prefix
#print axioms no_return_join_empty
#print axioms mapped_callback_raw

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
  let equal (name : String) (actual : Except String Json) (expected : Json) : IO Unit :=
    test (name ++ ": " ++ (match actual with | .error e => e | .ok _ => "returned"))
      (match actual with | .ok value => value == expected | _ => false)
  let refusal (name code : String) (actual : Except String Json) : IO Unit :=
    test name (match actual with | .error actual => actual == code | _ => false)
  let .ok (helpers, _) := (prepareHelpers [appendHelper, hugeHelper]).run {} |
    throw (IO.userError "repeat bounds helper preparation failed")

  for n in [0, 1, 3] do
    result s!"unused missing capture at count {n}"
      (transfer booleanSpec (.ret [1]) [.index (exact n), .boolean (some true), .absent])
      (some [.boolean (some true)])
    result s!"optional state remains optional at count {n}"
      (transfer booleanSpec (.ret [1])
        [.index (exact n), .optional (.boolean (some true)), .absent])
      (some [.optional (.boolean (some true))])
  result "active absent count has no successful path"
    (transfer booleanSpec (.ret [99]) [.absent, .absent, .absent]) none
  result "optional count uses only its successful present branch"
    (transfer booleanSpec (.ret [1])
      [.optional (.index (exact 2)), .boolean (some true), .absent])
    (some [.boolean (some true)])
  for n in [4, indexLimit, indexLimit * indexLimit] do
    result s!"wholly above maximum skips callback {n}"
      (transfer booleanSpec (.ret [99]) [.index (exact n), .absent, .absent]) none
  result "zero maximum admits only the zero branch"
    (transfer { booleanSpec with maximum := 0 } (.ret [99])
      [.index ⟨0, 9⟩, .boolean (some true), .absent]) (some [.boolean (some true)])
  result "positive lower endpoint above zero maximum has no result"
    (transfer { booleanSpec with maximum := 0 } (.ret [99])
      [.index ⟨1, 9⟩, .absent, .absent]) none
  result "outside skips missing count and malformed execution body"
    (transfer booleanSpec (.ret [99]) [.absent, .absent, .absent] {} 1) (some [.absent])
  result "outside does not depend on state scope well-formedness"
    (transfer { booleanSpec with stateScopes := [] } (.ret [99])
      [.index (exact indexLimit), .boolean (some true), .absent] {} 1) (some [.absent])
  result "zero state returns some empty tuple"
    (transfer emptySpec (.ret []) [.index (exact 2)]) (some [])
  result "zero-state missing count remains none"
    (transfer emptySpec (.ret []) [.absent]) none
  result "zero-state stopped prefixes remain conservative some empty tuple"
    (transfer emptySpec (.stop .abort) [.index ⟨0, 2⟩]) (some [])
  result "definite callback stop preserves initial prefix at exact positive count"
    (transfer booleanSpec (.stop .abort) [.index (exact 2), .boolean (some true), .absent])
    (some [.boolean (some true)])

  let masked := { booleanSpec with roles := [0, 1], stateScopes := [[1]] }
  result "zero masks initial state"
    (transfer masked (.ret [2]) [.index (exact 0), .boolean (some true), .boolean (some true)])
    (some [.absent])
  result "each successful yield is masked before prefix join"
    (transfer masked (.ret [2]) [.index (exact 3), .boolean (some true), .boolean (some true)])
    (some [.absent])
  result "optional capture stays optional when yielded"
    (transfer booleanSpec (.ret [2])
      [.index (exact 2), .absent, .optional (.boolean (some true))])
    (some [.optional (.boolean (some true))])
  let indices : RepeatSpec := ⟨[.index, .index], [.index], [0], [[0], [0]], 3⟩
  result "induction changes while original captured count stays fixed"
    (transfer indices (.ret [0, 3])
      [.index (exact 2), .index (exact 0), .index (exact 2), .index (exact 2)])
    (some [.index ⟨0, 1⟩, .index (exact 2)])

  let grow (bounds : Interval) := transfer vectorSpec appendBody
    [.index bounds, .vector (exact 0), .atom] (helpers := helpers)
  result "growth joins initial and all three prefixes even with positive lower count"
    (grow ⟨1, 3⟩) (some [.vector ⟨0, 3⟩])
  result "partial interval above maximum explores only the admissible upper bound"
    (grow ⟨2, 1000000⟩) (some [.vector ⟨0, 3⟩])
  let stopThird : RawRegion Ty ProtocolOp :=
    .letOp (.calculate (.indexConstant 2) rfl) [] [.index] .nil
      (.letOp (.calculate .indexEqual rfl) [0, 1] [.boolean] .nil
        (.letOp (.calculate (.booleanConstant false) rfl) [] [.boolean] .nil
          (.letOp (.calculate .booleanEqual rfl) [0, 1] [.boolean] .nil
            (.letOp (.guard 0 "beforeThird") [0] [] .nil
              (.letOp (.localCall appendHelper.helper rfl 0 "append") [5, 6]
                [vectorType] .nil (.ret [0]))))))
  result "stopping third step retains both grown prefixes"
    (transfer vectorSpec stopThird [.index ⟨1, 3⟩, .vector (exact 0), .atom]
      (helpers := helpers)) (some [.vector ⟨0, 2⟩])
  failure "growing state retains vector capacity"
    (transfer vectorSpec appendBody [.index (exact 2), .vector (exact 4095), .atom]
      (helpers := helpers)) .value
  let nested := repeatRegion vectorSpec appendBody [0, 1, 2] (.ret [0])
  result "nested callback receives the outer induction as its count"
    (transfer vectorSpec nested [.index (exact 3), .vector (exact 0), .atom]
      (helpers := helpers)) (some [.vector ⟨0, 3⟩])
  failure "nested growth also enforces vector capacity"
    (transfer vectorSpec nested [.index (exact 3), .vector (exact 4095), .atom]
      (helpers := helpers)) .value
  let guarded := RawRegion.letOp (.guard 0 "capture") [2] [] .nil (.ret [1])
  result "missing demanded capture stops that step without fabricating a yield"
    (transfer booleanSpec guarded [.index (exact 1), .boolean (some true), .absent])
    (some [.boolean (some true)])
  failure "conservative stopped prefix can keep a costly suffix reachable"
    (analyze (repeatRegion emptySpec (.stop .abort) [0] hugeBody)
      [.index (exact 1)] helpers) .work
  result "missing count prunes the suffix instead of returning empty state"
    (analyze (repeatRegion emptySpec (.ret []) [0] hugeBody) [.absent] helpers) none
  result "over-maximum count prunes the suffix"
    (analyze (repeatRegion emptySpec (.ret []) [0] hugeBody) [.index (exact 4)] helpers) none

  failure "planned work is charged before the callback can fail unknown"
    (transfer { emptySpec with maximum := 1048576 } (.ret [99])
      [.index (exact 1048576)]) .work
  failure "remaining work is checked before callback descent"
    (transfer emptySpec (.ret [99]) [.index (exact 2)]) .work { work := workLimit - 4 }
  failure "analysis capacity is independent of work"
    (transfer emptySpec (.ret []) [.index (exact 0)]) .analysis { analysis := analysisLimit }
  result "zero skips costly callback execution"
    (transfer emptySpec hugeBody [.index (exact 0)] (helpers := helpers)) (some [])
  result "outside skips costly callback execution"
    (transfer emptySpec hugeBody [.index (exact 3)] (self := 1) (helpers := helpers)) (some [])
  failure "positive zero-state body still incurs its helper work"
    (transfer emptySpec hugeBody [.index (exact 1)] (helpers := helpers)) .work
  let many := { emptySpec with maximum := 1000 }
  failure "nested repeat traversal shares the analysis meter"
    (transfer many
      (.letOp (.calculate (.indexConstant 1000) rfl) [] [.index] .nil
        (repeatRegion many (.ret []) [0] (.ret []))) [.index (exact 1000)]) .analysis

  failure "wrong complete argument arity" (transfer booleanSpec (.ret [1]) [.absent]) .unknown
  failure "invalid count type" (transfer emptySpec (.ret []) [.boolean none]) .unknown
  failure "reversed count interval" (transfer emptySpec (.ret []) [.index ⟨2, 1⟩]) .unknown
  failure "mismatched state scope arity"
    (transfer { booleanSpec with stateScopes := [] } (.ret [1])
      [.index (exact 0), .absent, .absent]) .unknown
  failure "returning callback cannot truncate state"
    (transfer booleanSpec (.ret []) [.index (exact 1), .absent, .absent]) .unknown
  for bodies in [RawRegions.nil,
      .cons [.index] [] (.ret []) (.cons [.index] [] (.ret []) .nil),
      .cons [] [] (.ret []) .nil, .cons [.index] [.boolean] (.ret []) .nil] do
    failure "repeat requires one callback with exact complete ABI"
      (Bounds.protocolOperation {} [] {} 0 noReplies (.repeat emptySpec "repeat")
        [.index (exact 0)] bodies) .unknown
  for (op, args) in [
      (ProtocolOp.mark "mark", []), (.guard 0 "gate", [Value.boolean none]),
      (.calculate (.booleanConstant true) rfl, []),
      (.exchange .boolean 0 1 "send", [.boolean none]),
      (.restrict .boolean [0], [.boolean none]),
      (.draw 0 scalarDomain "draw", [.atom]),
      (.localCall hugeHelper.helper rfl 0 "huge", []),
      (.protocolApply relaySignature [0, 1] "apply", [.absent]),
      (.statement "relation" [] [] 0, [])] do
    failure "callback-free operations reject an unexpected callback"
      (Bounds.protocolOperation helpers [] {} 0 noReplies op args (callback emptySpec (.ret []))) .unknown

  let context := ({} : ProtocolContext).enter "outer" [2, 0, 1]
  let mappedArgs : Env := [.index (exact 2), .vector (exact 7)]
  let prepare (definitions : List CheckedProtocol) (received : Ty → Analysis (Option Value))
      (self : Nat := 2) : Analysis Result := do
    let table ← prepareProtocols {} definitions
    invokeProtocolBound table mappedSignature context self received mappedArgs
  result "repeat inside application keeps root self and captured earlier table"
    (prepare [relay, mapped] (fun _ => pure (some (.vector (exact 19)))))
    (some [.optional (.vector (exact 19))])
  result "mapped nonreceiver state is absent"
    (prepare [relay, mapped] noReplies 0) (some [.absent])
  result "mapped repeat outsider never asks for a reply"
    (prepare [relay, mapped] (fun _ => throw .unknown) 1) (some [.absent])
  failure "callback cannot resolve a later protocol declaration"
    (prepare [mapped, relay] (fun _ => pure (some (.vector (exact 19))))) .unknown
  let envelope (replies : List ScriptReply) : Analysis Result := do
    let replies ← abstractReplies replies
    prepare [relay, mapped] (receiveBounds replies)
  result "repeat receives all typed replies including unrelated unused suffix"
    (envelope [receivedVector 3, receivedVector 23]) (some [.optional (.vector ⟨3, 23⟩)])
  result "missing reply keeps conservative initial prefix"
    (envelope []) (some [.absent])
  failure "oversized independent receive fails before joining"
    (prepare [relay, mapped] (fun _ => pure (some (.vector (exact 4097))))) .value
  failure "aliased result serialization charges each traversal"
    (do
      let result ← transfer vectorSpec (.ret [1])
        [.index (exact 0), .vector (exact 4096), .absent]
      let some [value] := result | throw .unknown
      (List.replicate 32 value).forM outputWork) .work

  equal "checked zero repeat skips missing captured guard"
    (runSource 3 (wireRequest "P" [.str "0", .bool true, .null])) (returned [.bool true])
  equal "checked missing count stops at retained header"
    (runSource 3 (wireRequest "P" [.null, .bool true, .null])) (stopped "incomplete" "repeat")
  equal "checked above-maximum count is refused rather than truncated"
    (runSource 3 (wireRequest "P" [.str "4", .bool true, .null])) (stopped "refused" "repeat")
  equal "checked missing demanded capture stops at callback guard"
    (runSource 3 (wireRequest "P" [.str "1", .bool true, .null])) (stopped "incomplete" "gate")
  equal "checked false capture stops despite conservative preflight return"
    (runSource 3 (wireRequest "P" [.str "2", .bool true, .bool false])) (stopped "reject" "gate")
  equal "checked true capture returns"
    (runSource 3 (wireRequest "P" [.str "3", .bool true, .bool true])) (returned [.bool true])
  equal "checked outside participant ignores absent operands"
    (runSource 3 (wireRequest "Q" [.null, .null, .null])) (returned [.null])
  refusal "observer constructor capacity remains separate" "structured-open-capacity"
    (runSource 3 (wireRequest "P" [.str "0", .bool true, .null] [] 1))
  refusal "admitted count can still exceed preflight work" "structured-open-work-limit"
    (runSource 1048576 (wireRequest "P" [.str "1048576", .bool true, .bool true]))
  refusal "u64 input decoding remains separate from logical count refusal"
    "structured-input-natural-range"
    (runSource 3 (wireRequest "P" [.str (toString indexLimit), .bool true, .null]))

  let response := arr [.str "value", .str "1"]
  let queries := [("prelude", response), ("draw", response), ("draw", response), ("suffix", response)]
  equal "zero-state iterations retain every effect at the same static label"
    (runService 2 queries)
    (arr [.str "zkc.structured-open-result/0", arr [.str "returned", arr []],
      arr (traceRecords queries), toJson queries.length])
  let zeroQueries := [("prelude", response), ("suffix", response)]
  equal "zero repeat retains earlier and later ordered actions"
    (runService 0 zeroQueries)
    (arr [.str "zkc.structured-open-result/0", arr [.str "returned", arr []],
      arr (traceRecords zeroQueries), toJson zeroQueries.length])
  let stoppingQueries := [("prelude", response), ("draw", response),
    ("draw", arr [.str "stop", .str "abort"])]
  equal "zero-state stop retains consumed prefix and suppresses later iterations and suffix"
    (runService 3 stoppingQueries)
    (arr [.str "zkc.structured-open-result/0", arr [.str "stopped", .str "abort", .str "draw"],
      arr (traceRecords stoppingQueries ++
        [arr [.str "stop", .str "abort", .str "draw", toJson stoppingQueries.length]]),
      toJson stoppingQueries.length])

  let failures ← failures.get
  unless failures.isEmpty do
    throw (IO.userError ("Structured repeat bounds failures:\n" ++
      String.intercalate "\n" failures.reverse))
  IO.println s!"Structured repeat bounds: {← count.get} controls passed"

#eval run

end Tests.StructuredRepeatBounds
