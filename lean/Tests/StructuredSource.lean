import Zkc.Source.Structured.Laws
import Zkc.Source.Structured.ClosedProfile
import Zkc.Source.Structured.ModelAdmission
import ZkcTools.StructuredSource.Evaluation
import ZkcTools.DeclarationAudit

/-! Synthetic checker/semantics controls. Actual-export fixtures and their
binding/proofs are owned by the structured bridge, not these unit tests. -/

-- Direct reduction avoids repeatedly unfolding the dependent admission equations.
set_option smartUnfolding false

namespace StructuredSourceTests
open Lean Zkc.Source Zkc.Source.Structured

local instance : BEq (Except String Json) where
  beq left right := match left, right with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def field : Ty := .field scalarDomain
def vector : Ty := .vector scalarDomain
def digest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')

def function (name : String) (kind : Kind) (inputs outputs : List Ty) (body : Block)
    (premises : List Bound := []) : Definition :=
  .function ⟨name, kind, if kind == .protocol then .publicDef else .privateDef, inputs, outputs,
    if kind == .protocol then some ⟨["P"], inputs.map (fun _ => ["P"]),
      outputs.map (fun _ => ["P"])⟩ else none, premises,
    match kind with
    | .math => none
    | .local => some (.local name [])
    | .protocol => some (.protocol ⟨name, []⟩), body⟩

def snapshot (definitions : List Definition) (domains : List Domain := []) : Snapshot :=
  (let contractDefinitions : List Definition := definitions
   ⟨digest, "main", domains, [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩)

def totalStep (returned : List Nat := [2, 0]) (container : Nat := 3)
    (premises : List Bound := [⟨2, 3, 0⟩]) : Definition :=
  function "step" .math [field, field, .index, vector] [field, field]
    (.block [.instruction (.boundedAt scalarDomain) [container, 2] [field] [] ""] (.ret returned)) premises

def totalRoot : Definition :=
  function "main" .protocol [vector, field, field] [field, field]
    (.block [.instruction (.fold "items" "step" "") [0, 1, 2] [field, field] [] ""] (.ret [0, 1]))

def total : Snapshot := snapshot [totalStep, totalRoot] [⟨"items", [vector], [.indices 0 0], 0⟩]

def unit (reason : PIR.Stop := .abort) : Snapshot := snapshot [
  function "step" .local [field, vector, .boolean] [] (.block [] (.stop reason "abort")),
  function "predicate" .local [field, vector, .boolean] [.boolean] (.block [] (.ret [2])),
  .finite ⟨"fold", .privateDef, [vector, .boolean], [], "items", "step", "predicate"⟩,
  function "work" .local [vector, .boolean] [.boolean]
    (.block [.instruction (.apply "fold") [0, 1] [] [] "fold"] (.ret [1])),
  function "main" .protocol [vector, .boolean] [.boolean]
    (.block [.instruction (.localCall "work" "P") [0, 1] [.boolean] [] "work"] (.ret [0]))]
  [⟨"items", [vector], [.elements 0], 0⟩]

def localProgram (inputs outputs : List Ty) (body : Block) : Snapshot := snapshot [
  function "work" .local inputs outputs body,
  function "main" .protocol inputs outputs
    (.block [.instruction (.localCall "work" "P") (List.range inputs.length) outputs [] "work"]
      (.ret (List.range outputs.length)))]

def boolean (value : Bool) : Json := .arr #[.str "bool", .bool value]
def scalar (value : Nat) : Json := .arr #[.str "field", .str scalarDomain, .str (toString value)]
def vec (values : List Nat) : Json :=
  .arr #[.str "vector", .str scalarDomain, .arr (values.map (fun x => .str (toString x))).toArray]
def index (value : Nat) : Json := .arr #[.str "index", toJson value]
def returned (values : List Json) : Json := .arr #[.str "returned", .arr values.toArray]
def stopped (reason : String) : Json := .arr #[.str "stopped", .str reason]

def evaluate (raw : Snapshot) (values : List Json) : Except String Json := do
  ZkcTools.StructuredSource.evaluate (← check raw) (.arr values.toArray)

def loop (conditional : Bool := false) (wrongCapture : Bool := false) : Snapshot :=
  let terminal := if conditional then Terminator.condition [0, 1, 4]
    else Terminator.yield [0, if wrongCapture then 2 else 3]
  let flipped : Block := .block [.instruction .branch [0] [.boolean]
    [.region [] [.boolean]
      (.block [.instruction (.booleanConstant false) [] [.boolean] [] "flip_false"] (.yield [0])),
     .region [] [.boolean]
      (.block [.instruction (.booleanConstant true) [] [.boolean] [] "flip_true"] (.yield [0]))]
    "flip"] (.yield [0])
  let instructions := [.instruction .branch [1, 2] [.boolean]
    [.region [.boolean] [.boolean] flipped,
     .region [.boolean] [.boolean] (.block [] (.yield [0]))] "xor"] ++
    if conditional then [.instruction (.booleanConstant false) [] [.boolean] [] "false"] else []
  localProgram [.index, .index, .boolean, .boolean] [.boolean]
    (.block [.instruction (if conditional then .loopCondition else .loop) [0, 1, 2, 3] [.boolean]
      [.region [.index, .boolean, .boolean] (if conditional then [.boolean, .boolean, .boolean]
          else [.boolean, .boolean])
        (.block instructions terminal)] "loop"] (.ret [0]))

def nested : Snapshot := localProgram [.boolean, field, field] [field, field]
  (.block [.instruction .branch [0, 1, 2] [field, field]
    [.region [field, field] [field, field] (.block [] (.yield [1, 0])),
     .region [field, field] [field, field] (.block [] (.yield [0, 1]))] "branch"] (.ret [0, 1]))

def zeroResult : Snapshot := localProgram [.boolean] [.boolean]
  (.block [.instruction .branch [0] []
    [.region [] [] (.block [] (.stop .reject "reject")),
     .region [] [] (.block [] (.yield []))] "branch"] (.ret [0]))

def shared : Snapshot := snapshot [
  function "main" .protocol [field, field] [field, field]
    (.block [.instruction (.call "swap") [0, 1] [field, field] [] "",
      .instruction (.call "swap") [0, 1] [field, field] [] ""] (.ret [0, 1])),
  function "swap" .math [field, field] [field, field] (.block [] (.ret [1, 0]))]

def preconditionCall (wrong : Bool) : Snapshot :=
  snapshot [
    function "read" .math [.index, vector] [field]
      (.block [.instruction (.boundedAt scalarDomain) [1, 0] [field] [] ""] (.ret [0])) [⟨0, 1, 0⟩],
    function "step" .math [field, .index, vector, vector] [field]
      (.block [.instruction (.call "read") [1, if wrong then 3 else 2] [field] [] ""] (.ret [0]))
      [⟨1, 2, 0⟩],
    function "main" .protocol [vector, field, vector] [field]
      (.block [.instruction (.fold "items" "step" "") [0, 1, 2] [field] [] ""] (.ret [0]))]
    [⟨"items", [vector], [.indices 0 0], 0⟩]

def refused (raw : Snapshot) (code : String) : Bool :=
  match check raw with | .error actual => actual == code | .ok _ => false

def forwardedBound (direct wrong : Bool) : Snapshot := snapshot [
  function "echo" .math [vector, vector, .index] [vector, .index, vector]
    (.block [] (.ret [if wrong then 1 else 0, 2, if wrong then 1 else 0])),
  function "again" .math [vector, vector, .index] [vector, .index]
    (.block [.instruction (.call "echo") [0, 1, 2] [vector, .index, vector] [] ""] (.ret [2, 1])),
  function "read" .math [vector, .index] [field]
    (.block [.instruction (.boundedAt scalarDomain) [0, 1] [field] [] ""] (.ret [0])) [⟨1, 0, 0⟩],
  function "step" .math [field, .index, vector, vector] [field]
    (.block [.instruction (.call "again") [2, 3, 1] [vector, .index] [] "",
      .instruction (if direct then .boundedAt scalarDomain else .call "read")
        [0, 1] [field] [] ""] (.ret [0])) [⟨1, 2, 0⟩],
  function "main" .protocol [vector, field, vector] [field]
    (.block [.instruction (.fold "items" "step" "") [0, 1, 2] [field] [] ""] (.ret [0]))]
  [⟨"items", [vector], [.indices 0 0], 0⟩]

/-- The selected vector is also passed as capture C; recurrent state is separate. -/
def aliasedCapture (same : Bool) : Snapshot := snapshot [
  function "step" .math [field, .index, vector, vector] [field]
    (.block [.instruction (.boundedAt scalarDomain) [3, 1] [field] [] ""] (.ret [0])) [⟨1, 3, 0⟩],
  function "main" .protocol [vector, vector, field] [field]
    (.block [.instruction (.fold "items" "step" "") [0, 2, if same then 0 else 1]
      [field] [] ""] (.ret [0]))] [⟨"items", [vector], [.indices 0 0], 0⟩]

def stateBound : Snapshot := snapshot [
  function "step" .math [vector, .index, vector] [vector]
    (.block [.instruction (.boundedAt scalarDomain) [0, 1] [field] [] ""] (.ret [1])) [⟨1, 0, 0⟩],
  function "main" .protocol [vector] [vector]
    (.block [.instruction (.fold "items" "step" "") [0, 0] [vector] [] ""] (.ret [0]))]
  [⟨"items", [vector], [.indices 0 0], 0⟩]

/-- Both a helper summary and its caller must compare canonical identities,
while an unrelated same-typed vector must remain distinct at either boundary. -/
def selectedBound (wrongHelper wrongCaller : Bool) : Snapshot := snapshot [
  function "echo" .math [vector] [vector] (.block [] (.ret [0])),
  function "choose" .math [vector, vector, .boolean] [vector]
    (.block [.instruction (.call "echo") [0] [vector] [] "",
      .instruction (.select vector) [3, 0, if wrongHelper then 2 else 1] [vector] [] ""] (.ret [0])),
  function "step" .math [field, .index, vector, vector, .boolean] [field]
    (.block [.instruction (.call "choose") [2, 3, 4] [vector] [] "",
      .instruction (.select vector) [5, 0, if wrongCaller then 4 else 3] [vector] [] "",
      .instruction (.boundedAt scalarDomain) [0, 3] [field] [] ""] (.ret [0])) [⟨1, 2, 0⟩],
  function "main" .protocol [vector, vector, .boolean, field] [field]
    (.block [.instruction (.fold "items" "step" "") [0, 3, 1, 2] [field] [] ""] (.ret [0]))]
  [⟨"items", [vector], [.indices 0 0], 0⟩]

def dependencyChain (length copies : Nat) : Snapshot :=
  let helpers := (List.range length).map fun n =>
    let name := "helper" ++ toString n
    let instructions := if n == 0 then [] else
      List.replicate copies (.instruction (.call ("helper" ++ toString (n - 1))) [] [] [] "")
    function name .math [] [] (.block instructions (.ret []))
  snapshot (helpers ++ [function "main" .protocol [] []
    (.block [.instruction (.call ("helper" ++ toString (length - 1))) [] [] [] ""] (.ret []))])

/-- Inspect a fully linked model without the native expansion policy. -/
private def dependencyPhases (source : Snapshot) :
    Except String (List CheckedDefinition × List CheckedProtocol) := do
  let payload ← checkFormedPayload source
  return (payload.definitions, payload.protocols)

-- Kernel checks use reduction, never native_decide or an evaluator oracle.
theorem total_admitted : (checkClosed total).isOk = true := by decide +kernel
theorem wrong_call_refused : refused (preconditionCall true) "structured-call-premise" = true := by decide +kernel
theorem wrong_capture_refused : refused (loop false true) "structured-capture-forwarding" = true := by decide +kernel

def totalImported : ClosedImported total := closedImportedOfIsOk total total_admitted

theorem total_exact_subject : totalImported.program.snapshot = total :=
  totalImported.exactSubject

-- The structured admission, checked-data and law modules, and every theorem of
-- this file so far, have axiom closures within `propext`, `Classical.choice`
-- and `Quot.sound`.
run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.Structured.Import, `Zkc.Source.Structured.CheckedData, `Zkc.Source.Structured.Laws]
    "STRUCTURED-SOURCE-LAWS-AUDIT-PASS" (exactModules := true)

run_cmd ZkcTools.DeclarationAudit.checkCurrent "STRUCTURED-SOURCE-CONTROLS-AXIOM-PASS"

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test := fun (name : String) (passed : Bool) => do
    count.modify (· + 1)
    unless passed do failures.modify (name :: ·)
  test "total-empty" (evaluate total [vec [], scalar 5, scalar 7] == .ok (returned [scalar 5, scalar 7]))
  test "total-one" (evaluate total [vec [11], scalar 5, scalar 7] == .ok (returned [scalar 7, scalar 11]))
  test "total-three" (evaluate total [vec [11, 13, 17], scalar 5, scalar 7] == .ok (returned [scalar 13, scalar 17]))
  test "reordered-results-distinct" (evaluate {total with definitions := [totalStep [0, 2], totalRoot]}
    [vec [11], scalar 5, scalar 7] == .ok (returned [scalar 11, scalar 7]))
  test "unit-empty-enabled" (evaluate unit [vec [], boolean true] == .ok (returned [boolean true]))
  test "unit-disabled" (evaluate unit [vec [11, 13], boolean false] == .ok (returned [boolean false]))
  test "unit-abort" (evaluate unit [vec [11], boolean true] == .ok (stopped "abort"))
  test "changed-stop" (evaluate (unit .reject) [vec [11], boolean true] == .ok (stopped "reject"))
  test "sharing" (evaluate shared [scalar 11, scalar 19] == .ok (returned [scalar 11, scalar 19]))
  test "one-stored-helper" (match check shared with
    | .ok p => p.payload.definitions.length == 1 && p.payload.protocols.length == 1
    | _ => false)
  test "call-premise-positive" (evaluate (preconditionCall false) [vec [11, 13], scalar 5, vec [29, 31]] ==
    .ok (returned [scalar 13]))
  test "same-type-wrong-container" (refused (preconditionCall true) "structured-call-premise")
  for direct in [false, true] do
    test "forwarded-reordered-repeated-bound" (evaluate (forwardedBound direct false)
      [vec [11, 13], scalar 5, vec [29]] == .ok (returned [scalar 13]))
    test "forwarded-unrelated-container-refused" (refused (forwardedBound direct true)
      (if direct then "structured-bounded-at-premise" else "structured-call-premise"))
  test "aliased-domain-capture" (evaluate (aliasedCapture true)
    [vec [11, 13], vec [], scalar 5] == .ok (returned [scalar 13]))
  test "distinct-domain-capture-refused" (refused (aliasedCapture false) "structured-fold-premise")
  test "initial-state-equality-is-not-invariant" (refused stateBound "structured-fold-premise")
  for flag in [false, true] do
    test "select-known-alias-through-helper-and-caller" (evaluate (selectedBound false false)
      [vec [11, 13], vec [], boolean flag, scalar 7] == .ok (returned [scalar 13]))
  for (helper, caller) in [(true, false), (false, true), (true, true)] do
    test "select-unrelated-container-refused" (refused (selectedBound helper caller)
      "structured-bounded-at-premise")
  test "static-budget-counts-finite-declaration" (!unit.instructionsWithin 3 && unit.instructionsWithin 4)
  test "oversized-math-refused-before-summary" (refused (snapshot [
    function "oversized" .math [] []
      (.block (List.replicate 4097 (.instruction (.booleanConstant true) [] [.boolean] [] "")) (.ret [])),
    function "main" .protocol [] [] (.block [] (.ret []))]) "structured-instruction-limit")
  test "missing-premise" (refused {total with definitions := [totalStep [2, 0] 3 [], totalRoot]}
    "structured-bounded-at-premise")
  test "precondition-axis" (refused {total with definitions := [totalStep [2, 0] 3 [⟨2, 3, 1⟩], totalRoot]}
    "structured-header")
  test "domain-axis" (refused {total with domains := [⟨"items", [vector], [.indices 0 1], 0⟩]} "structured-domain-axis")
  test "unused-domain" (refused {total with domains := total.domains ++ [⟨"bad", [field], [.elements 0], 0⟩]}
    "structured-domain-container")
  test "dormant-body" (refused {total with definitions := total.definitions ++
    [function "bad" .math [] [field] (.block [] (.ret [0]))]} "structured-formation")
  test "dormant-math-stop" (refused {total with definitions := total.definitions ++
    [function "bad" .math [] [] (.block [] (.stop .abort "stop"))]} "structured-math-stop")
  test "cycle" (refused (snapshot [function "main" .protocol [] [] (.block [] (.ret [])),
    function "cycle" .math [] [] (.block [.instruction (.call "cycle") [] [] [] ""] (.ret []))])
    "structured-helper-cycle")
  test "reference-depth" (refused (dependencyChain 66 1) "structured-reference-depth")
  test "root-reference-depth" (refused (dependencyChain 65 1) "structured-reference-depth")
  let dag := dependencyChain 17 2
  let formedDag : Except String (List CheckedDefinition) := do
    let summaries ← dag.identitySummaries
    let definitions ← (dag.definitions.filter (·.kind != .protocol)).mapM
      (checkDefinition dag [] summaries)
    return (← orderDefinitions definitions.length definitions []).map (·.definition)
  test "shared-dag-is-not-expanded-for-formation" (match formedDag with
    | .ok definitions => definitions.length == 17 &&
        (definitions.map (·.instructionCount)).foldl (· + ·) 0 == 32
    | .error _ => false)
  let availableDag : Except String Unit := do
    let (definitions, protocols) ← dependencyPhases dag
    checkUnitAvailability definitions protocols
  test "shared-dag-availability-admitted" availableDag.isOk
  test "shared-dag-native-work-refused" (refused dag "structured-application-limit")
  test "shared-dag-model-admitted" (checkFormedPayload dag).isOk
  let missingEntry := { dag with entry := "missing" }
  test "native-budget-precedes-entry-refusal"
    (refused missingEntry "structured-application-limit")
  test "model-still-checks-entry" (match checkFormedPayload missingEntry with
    | .error code => code == "structured-entry"
    | .ok _ => false)
  let deepDag := dependencyChain 40 2
  let availableDeepDag : Except String Unit := do
    let (definitions, protocols) ← dependencyPhases deepDag
    checkUnitAvailability definitions protocols
  test "empty-summary-dag-does-not-expand-operations" availableDeepDag.isOk
  -- Test the existing abstract phase directly: whole-unit native budgets now
  -- refuse this Math DAG before execution, while the analysis meter is distinct.
  let deepAnalysis : Except String Unit := do
    let (definitions, protocols) ← dependencyPhases deepDag
    let [root] := protocols | throw "unexpected-test-protocols"
    let raw ← closedRootTree root.raw
    let analysis : ZkcTools.StructuredSource.Bounds.Analysis Unit := do
      let helpers ← ZkcTools.StructuredSource.Bounds.prepareHelpers definitions
      let _ ← ZkcTools.StructuredSource.Bounds.region
        (ZkcTools.StructuredSource.Bounds.operation helpers) raw []
      pure ()
    (analysis.run' {}).mapError (ZkcTools.StructuredSource.Bounds.Failure.code false)
  test "shared-dag-analysis-limit-is-separate" (deepAnalysis ==
    .error "structured-bounds-analysis-limit")
  test "empty-summary-dag-native-work-refused"
    (refused deepDag "structured-application-limit")
  test "reference-depth-boundary" ((dependencyPhases (dependencyChain 64 1)).isOk)
  test "native-node-depth-overflow" (refused (dependencyChain 64 1) "structured-application-depth")
  test "native-node-depth-boundary" ((check (dependencyChain 63 1)).isOk)
  test "declaration-order-does-not-change-fold" (evaluate
    {unit with definitions := unit.definitions.reverse} [vec [2], boolean true] == .ok (stopped "abort"))
  let hiddenCycle := snapshot [
    function "main" .protocol [] [] (.block [] (.ret [])),
    function "hidden" .local [.boolean] [] (.block [.instruction .branch [0] []
      [.region [] [] (.block [.instruction (.apply "again") [] [] [] "call"] (.yield [])),
       .region [] [] (.block [] (.yield []))] "branch"] (.ret [])),
    function "again" .local [] [] (.block [
      .instruction (.booleanConstant false) [] [.boolean] [] "false",
      .instruction (.apply "hidden") [0] [] [] "back"] (.ret []))]
  test "nested-dormant-helper-cycle" (refused hiddenCycle "structured-helper-cycle")
  let inventory := (check unit).toOption.map fun program =>
    program.payload.definitions.map fun definition =>
      (definition.name, definition.dependencies, definition.instructionCount)
  test "dependencies-derived-from-formed-bodies" (inventory == some [
    ("step", [], 1), ("predicate", [], 0), ("fold", ["step", "predicate"], 1),
    ("work", ["fold"], 2)])
  test "direct-wrong-container" (refused (snapshot [
    function "main" .protocol [] [] (.block [] (.ret [])),
    function "bad" .math [.index, vector, vector] [field]
      (.block [.instruction (.boundedAt scalarDomain) [2, 0] [field] [] ""] (.ret [0])) [⟨0, 1, 0⟩]])
    "structured-bounded-at-premise")
  test "unknown-helper" (refused (snapshot [function "main" .protocol [] []
    (.block [.instruction (.call "missing") [] [] [] ""] (.ret []))]) "structured-unknown-helper")
  test "wrong-helper-signature" (refused (snapshot [
    function "read" .math [field] [field] (.block [] (.ret [0])),
    function "main" .protocol [.boolean] [field]
      (.block [.instruction (.call "read") [0] [field] [] ""] (.ret [0]))]) "structured-formation")
  test "wrong-helper-kind" (refused (snapshot [
    function "helper" .local [] [] (.block [] (.ret [])),
    function "main" .protocol [] []
      (.block [.instruction (.call "helper") [] [] [] ""] (.ret []))]) "structured-call-kind")
  test "definition-limit" (refused (dependencyChain 128 1) "structured-table-limit")
  test "missing-local-origin" (refused (snapshot [
    .function ⟨"bad", .local, .privateDef, [], [], none, [], none, .block [] (.ret [])⟩,
    function "main" .protocol [] [] (.block [] (.ret []))]) "structured-header")
  test "protocol-stop-refused" (refused (snapshot [
    function "main" .protocol [] [] (.block [] (.stop .abort "stop"))]) "structured-protocol-terminator")
  test "public-math-refused" (refused (snapshot [
    .function ⟨"helper", .math, .publicDef, [], [], none, [], none, .block [] (.ret [])⟩,
    function "main" .protocol [] [] (.block [] (.ret []))]) "structured-header")
  for bindings in [[("N", "7"), ("N", "8")], [("N", "")]] do
    test "invalid-origin-bindings-refused" (refused (snapshot [
      .function ⟨"helper", .local, .privateDef, [], [], none, [], some (.local "template" bindings),
        .block [] (.ret [])⟩,
      function "main" .protocol [] [] (.block [] (.ret []))]) "structured-header")
  test "duplicate-symbol" (refused {total with definitions := total.definitions ++ [totalRoot]}
    "structured-duplicate-symbol")
  test "wrong-owner" (refused (snapshot [function "work" .local [] [] (.block [] (.ret [])),
    function "main" .protocol [] [] (.block [.instruction (.localCall "work" "V") [] [] [] "call"] (.ret []))])
    "structured-role")
  test "math-local-invoke" (refused (snapshot [function "work" .local [] [] (.block [] (.ret [])),
    function "main" .protocol [] [] (.block [] (.ret [])),
    function "bad" .math [] [] (.block [.instruction (.apply "work") [] [] [] ""] (.ret []))])
    "structured-math-operation")
  test "protocol-read-ownership" (refused (snapshot [
    function "main" .protocol [vector, .index] [field]
      (.block [.instruction (.boundedAt scalarDomain) [0, 1] [field] [] ""] (.ret [0]))])
    "structured-protocol-operation")
  test "conditional-loop-unconditional-stop-refused" (refused (localProgram
    [.index, .index, .boolean] [.boolean]
    (.block [.instruction .loopCondition [0, 1, 2] [.boolean]
      [.region [.index, .boolean] [.boolean, .boolean]
        (.block [] (.stop .abort "stop"))] "loop"] (.ret [0]))) "structured-terminator-kind")
  let nestedStop := localProgram [.index, .index, .boolean] [.boolean]
    (.block [.instruction .loopCondition [0, 1, 2] [.boolean]
      [.region [.index, .boolean] [.boolean, .boolean]
        (.block [.instruction .branch [1] []
          [.region [] [] (.block [] (.stop .abort "stop")),
           .region [] [] (.block [] (.yield []))] "branch"] (.condition [1, 1]))] "loop"] (.ret [0]))
  test "conditional-loop-nested-stop" (evaluate nestedStop [index 0, index 3, boolean true] ==
    .ok (stopped "abort"))
  test "conditional-loop-nested-continue" (evaluate nestedStop [index 0, index 3, boolean false] ==
    .ok (returned [boolean false]))
  test "loop-capture-forwarding" ((check (loop false false)).isOk)
  test "loop-wrong-capture" (refused (loop false true) "structured-capture-forwarding")
  test "loop-zero" (evaluate (loop false false) [index 5, index 2, boolean false, boolean true] ==
    .ok (returned [boolean false]))
  test "loop-two" (evaluate (loop false false) [index 0, index 2, boolean false, boolean true] ==
    .ok (returned [boolean false]))
  test "loop-one" (evaluate (loop false false) [index 0, index 1, boolean false, boolean true] ==
    .ok (returned [boolean true]))
  test "conditional-false-commits-state" (evaluate (loop true false)
    [index 0, index 2, boolean false, boolean true] == .ok (returned [boolean true]))
  test "nested-multi-yes" (evaluate nested [boolean true, scalar 3, scalar 7] == .ok (returned [scalar 7, scalar 3]))
  test "nested-multi-no" (evaluate nested [boolean false, scalar 3, scalar 7] == .ok (returned [scalar 3, scalar 7]))
  test "zero-result-still-stops" (evaluate zeroResult [boolean true] == .ok (stopped "reject"))
  test "zero-result-continues" (evaluate zeroResult [boolean false] == .ok (returned [boolean false]))
  test "closed-region-no-outer-access" (refused (localProgram [field] [field]
    (.block [.instruction .branch [] [field]
      [.region [] [field] (.block [] (.yield [0])),
       .region [] [field] (.block [] (.yield [0]))] "if"] (.ret [0]))) "structured-formation")
  test "duplicate-sites-across-arms" (refused (localProgram [.boolean] []
    (.block [.instruction .branch [0] []
      [.region [] [] (.block [] (.stop .abort "same")),
       .region [] [] (.block [] (.stop .reject "same"))] "if"] (.ret []))) "structured-duplicate-site")
  let guarded := snapshot [function "main" .protocol [.boolean] []
    (.block [.instruction (.guard "P") [0] [] [] "guard"] (.ret []))]
  test "guard-reject" (evaluate guarded [boolean false] == .ok (stopped "reject"))
  test "guard-return" (evaluate guarded [boolean true] == .ok (returned []))
  test "guard-wrong-owner" (refused (snapshot [function "main" .protocol [.boolean] []
    (.block [.instruction (.guard "V") [0] [] [] "guard"] (.ret []))]) "structured-role")
  test "local-field-arithmetic-refused" (refused (localProgram [field, field] [field]
    (.block [.instruction (.fieldAdd scalarDomain) [0, 1] [field] [] ""] (.ret [0])))
    "structured-local-operation")
  test "local-math-call-refused" (refused (snapshot [
    function "math" .math [] [] (.block [] (.ret [])),
    function "work" .local [] [] (.block [.instruction (.call "math") [] [] [] ""] (.ret [])),
    function "main" .protocol [] [] (.block [] (.ret []))]) "structured-local-operation")
  test "pure-protocol-site-refused" (refused (snapshot [function "main" .protocol [] [.boolean]
    (.block [.instruction (.booleanConstant true) [] [.boolean] [] "extra"] (.ret [0]))])
    "structured-pure-site")
  for (name, descriptor, a, b, expected) in [
      ("field-add-wrap", Descriptor.fieldAdd scalarDomain, scalarModulus - 1, 2, scalar 1),
      ("field-subtract-wrap", Descriptor.fieldSubtract scalarDomain, 1, 2, scalar (scalarModulus - 1)),
      ("field-multiply", Descriptor.fieldMultiply scalarDomain, 123456789, 987654321, scalar 121932631112635269)] do
    let program := snapshot [function "main" .protocol [field, field] [field]
      (.block [.instruction descriptor [0, 1] [field] [] ""] (.ret [0]))]
    test name (evaluate program [scalar a, scalar b] == .ok (returned [expected]))
  test "field-equal" (evaluate (snapshot [function "main" .protocol [field, field] [.boolean]
    (.block [.instruction (.fieldEqual scalarDomain) [0, 1] [.boolean] [] ""] (.ret [0]))])
    [scalar 17, scalar 17] == .ok (returned [boolean true]))
  test "field-constant" (evaluate (snapshot [function "main" .protocol [] [field]
    (.block [.instruction (.fieldConstant scalarDomain "19") [] [field] [] ""] (.ret [0]))])
    [] == .ok (returned [scalar 19]))
  test "field-constant-invalid" (refused (snapshot [function "main" .protocol [] [field]
    (.block [.instruction (.fieldConstant scalarDomain "019") [] [field] [] ""] (.ret [0]))])
    "structured-decimal")
  for (name, descriptor, expected) in [("boolean-and", Descriptor.booleanAnd, false),
      ("boolean-or", .booleanOr, true), ("boolean-xor", .booleanXor, true),
      ("boolean-equal", .booleanEqual, false), ("boolean-not-equal", .booleanNotEqual, true)] do
    let program := snapshot [function "main" .protocol [.boolean, .boolean] [.boolean]
      (.block [.instruction descriptor [0, 1] [.boolean] [] ""] (.ret [0]))]
    test name (evaluate program [boolean true, boolean false] == .ok (returned [boolean expected]))
  test "select-vector" (evaluate (snapshot [function "main" .protocol [.boolean, vector, vector] [vector]
    (.block [.instruction (.select vector) [0, 1, 2] [vector] [] ""] (.ret [0]))])
    [boolean false, vec [11], vec [19]] == .ok (returned [vec [19]]))
  test "input-field-canonical" (evaluate total [vec [], scalar scalarModulus, scalar 0] ==
    .error "structured-input-field-canonical")
  test "input-vector-limit" (evaluate unit [vec (List.replicate 4097 1), boolean false] ==
    .error "structured-list-limit")
  test "input-index-limit" (evaluate (loop false false) [index indexLimit, index 0, boolean true, boolean true] ==
    .error "structured-number-limit")
  test "evaluation-work-limit" (evaluate (loop false false)
    [index 0, index (2 ^ 20 + 1), boolean true, boolean true] == .error "structured-evaluation-work-limit")
  for (name, text) in [("json-object", "{}"), ("json-exponent", "[1e2]"),
      ("json-negative-zero", "[-0]"), ("json-trailing", "[] []"),
      ("json-depth", String.ofList (List.replicate 65 '[' ++ List.replicate 65 ']'))] do
    test name (!(Structured.Format.parse text).isOk)
  -- Identities decode as strings; admission resolves them against catalogue rows.
  test "unknown-service-decoded" ((Structured.Format.type (.arr #[.str "service", .str "rng"])).isOk)
  test "unknown-service-refused" (refused (snapshot [function "main" .protocol [.service "rng"] []
    (.block [] (.ret []))]) "structured-service-contract")
  test "unknown-opcode" (!(Structured.Format.descriptor (.arr #[.str "provider.call"])).isOk)
  test "extra-op-field" (!(Structured.Format.descriptor (.arr #[.str "bool.and", .str "extra"])).isOk)
  test "extra-domain-op" (!(Structured.Format.domain (.arr #[.str "domain", .str "items",
    .arr #[.arr #[.str "vector", .str scalarDomain]],
    .arr #[.arr #[.str "elements", toJson (0 : Nat), .str "extra"]], toJson (0 : Nat)])).isOk)
  test "origin-bindings-retained" (match Structured.Format.origin .local
      (.arr #[.str "template", .arr #[.arr #[.str "N", .str "7"], .arr #[.str "F", .str scalarDomain]]]) with
    | .ok value => value == some (.local "template" [("N", "7"), ("F", scalarDomain)])
    | _ => false)
  test "origin-string-path-refused" (!(Structured.Format.origin .local
    (.arr #[.str "template", .arr #[.str "legacy-path"]])).isOk)
  test "unknown-domain-decoded" ((Structured.Format.type (.arr #[.str "field", .str "F97"])).isOk)
  test "unknown-domain-refused" (refused (snapshot [function "main" .protocol [.field "F97"] []
    (.block [] (.ret []))]) "structured-domain-unknown")
  test "overlong-string" (!(Structured.Format.string (.str (String.ofList (List.replicate 513 'a')))).isOk)
  test "reference-limit" (!(Structured.Format.refs (.arr #[toJson (4097 : Nat)])).isOk)
  test "numeric-token-limit" (!(Structured.Format.parse
    ("[" ++ String.ofList (List.replicate 1025 '1') ++ "]")).isOk)
  test "snapshot-byte-limit" (!(Structured.Format.parse (String.ofList (List.replicate (1024 * 1024 + 1) ' '))).isOk)
  let failures ← failures.get
  unless failures.isEmpty do throw (IO.userError s!"structured failures: {failures.reverse}")
  IO.println s!"structured-source: {← count.get} focused checks passed"

end StructuredSourceTests

#eval StructuredSourceTests.run
