import ZkcTools.StructuredSource.OpenEvaluation

/-! Counterexamples for executable capacity, plus admitted programs evaluated
through the existing interpreter. These controls do not prove bound soundness. -/

namespace Tests.StructuredBounds
open Lean Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource
open Bounds

private def arr (xs : List Json) : Json := .arr xs.toArray
private def index (n : Nat) : Json := arr [.str "index", toJson n]
private def field (n : Nat) : Json := arr [.str "field", .str scalarDomain, .str (toString n)]
private def vector (n : Nat) : Json := arr [.str "vector", .str scalarDomain,
  arr (List.replicate n (.str "0"))]
private def vectorValues (xs : List Nat) : Json := arr [.str "vector", .str scalarDomain,
  arr (xs.map (fun n => .str (toString n)))]
private def returned (xs : List Json) : Json := arr [.str "returned", arr xs]
private def vectorTy : Ty := .vector scalarDomain
private def fieldTy : Ty := .field scalarDomain
private def maximum : Nat := indexLimit - 1

private def binding (name contract : String) (domain : Bool := false) : Binding :=
  ⟨name, contract, if domain then [scalarDomain] else [], ""⟩
private def exec (name binding : String) (args : List Nat) (out : List Ty)
    (parameters : List String := []) : Instruction :=
  .instruction (.exec "exec.apply" binding parameters) args out [] name
private def constant (n : Nat) : Instruction :=
  exec "index_constant" "constant" [] [.index] [toString n]
private def labelBlock : Nat → String → Block → Block
  | 0, _, body => body
  | depth + 1, sitePrefix, .block instructions terminal => .block
      (instructions.zipIdx.map fun (.instruction op args outputs regions _, i) =>
        let site := sitePrefix ++ "." ++ toString i
        .instruction op args outputs (regions.zipIdx.map fun (.region inputs outputs body, j) =>
          .region inputs outputs (labelBlock depth (site ++ "." ++ toString j) body)) site) terminal
private def helper (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .local, .privateDef, inputs, outputs, none, [], some (.local name []),
    labelBlock 32 name body⟩
private def program (bindings : List Binding) (inputs outputs : List Ty) (body : Block)
    (helpers : List Definition := []) : Snapshot :=
  (let contractDefinitions : List Definition := helpers ++ [helper "work" inputs outputs body,
      .function ⟨"main", .protocol, .publicDef, inputs, outputs,
        some ⟨["P"], inputs.map (fun _ => ["P"]), outputs.map (fun _ => ["P"])⟩, [], some (.protocol ⟨"main", []⟩),
        .block [.instruction (.localCall "work" "P") (List.range inputs.length) outputs [] "work"]
          (.ret (List.range outputs.length))⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], bindings, contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
private def runClosed (source : Snapshot) (inputs : List Json := []) : Except String Json := do
  evaluate (← check source) (arr inputs)
private def openRequest (inputs : List Json) (replies : List Json := []) : Json :=
  arr [.str "zkc.structured-open-request/0", .str "P", arr inputs, arr replies, toJson workLimit]
private def runOpen (source : Snapshot) (inputs : List Json := []) : Except String Json := do
  evaluateOpen (← check source) (openRequest inputs)
private def hasOpenReturn (actual : Except String Json) (values : List Json) : Bool :=
  match actual with
  | .ok (.arr result) =>
      result.size == 4 && result[1]? == some (arr [.str "returned", arr values]) &&
        result[3]? == some (toJson (1 : Nat))
  | _ => false

private def emptyLoop (lo hi : Nat) : Instruction :=
  .instruction .loop [lo, hi] [] [.region [.index] [] (.block [] (.yield []))] "loop"
private def constants := [binding "constant" "index.constant"]
private def constantProgram (n : Nat) : Snapshot := program constants [] [.index]
  (.block [constant n] (.ret [0]))
private def generatedLoop (n : Nat) (lower : Nat := 0) : Snapshot := program constants [] []
  (.block [constant n, constant lower, emptyLoop 0 1] (.ret []))

private def appendProgram : Snapshot := program [binding "append" "vector.append" true]
  [vectorTy, fieldTy] [vectorTy]
  (.block [exec "vector_append" "append" [0, 1] [vectorTy]] (.ret [0]))

private def growingProgram : Snapshot := program
  (constants ++ [binding "append" "vector.append" true, binding "length" "vector.length" true])
  [vectorTy, fieldTy, .index] [.index]
  (.block [constant 0,
    .instruction .loop [0, 3, 1, 2] [vectorTy]
      [.region [.index, vectorTy, fieldTy] [vectorTy, fieldTy]
        (.block [exec "vector_append" "append" [1, 2] [vectorTy]] (.yield [0, 3]))] "grow",
    exec "vector_length" "length" [0] [.index], emptyLoop 2 0] (.ret [0]))

private def raw (body : RawRegion Ty Op) (args : Env := []) : Except Failure (Result × Meter) :=
  (Bounds.region (Bounds.operation {}) body args).run {}
private def rawLoop (lo hi : Nat) (body : RawRegion Ty Op := .ret []) : RawRegion Ty Op :=
  .letOp (.indexConstant lo) [] [.index] .nil
    (.letOp (.indexConstant hi) [] [.index] .nil
      (.letOp (.loop [] []) [1, 0] [] (.cons [.index] [] body .nil) (.ret [])))

private def mathHelper (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none, body⟩

private def mapProgram (mask : List Bool) (body : Block)
    (helpers : List Definition := []) : Snapshot :=
  let spec : MapSpec := ⟨"formula", scalarDomain, mask⟩
  program [] spec.arguments [vectorTy]
    (.block [.instruction (.apply "mapping") (List.range mask.length) [vectorTy] [] "map"]
      (.ret [0]))
    (helpers ++ [mathHelper "formula" spec.scalarInputs [fieldTy] body,
      .map ⟨"mapping", spec.arguments, [vectorTy], "formula", mask⟩])

private def constantFormula : Block :=
  .block [.instruction (.fieldConstant scalarDomain "7") [] [fieldTy] [] ""] (.ret [0])

private def repeatedFormula (count : Nat) : Block :=
  .block (List.replicate count
    (.instruction (.fieldAdd scalarDomain) [0, 0] [fieldTy] [] "")) (.ret [0])

/-- Compare the existing interpreter's actual return with abstract membership;
do not compute expected primitive outputs with a second evaluator. -/
private def containsValue : Value → Value → Bool
  | .optional bound, actual => containsValue bound actual
  | .index bound, .index actual | .vector bound, .vector actual =>
      bound.lower ≤ actual.lower && actual.upper ≤ bound.upper
  | .boolean none, .boolean _ => true
  | .boolean (some bound), .boolean (some actual) => bound == actual
  | .atom, .atom => true
  | _, _ => false

private def containsValues : Env → Env → Bool
  | [], [] => true
  | bound :: bounds, actual :: actuals => containsValue bound actual && containsValues bounds actuals
  | _, _ => false

private def containsReturn (source : Snapshot) (json : List Json) : Except String Bool := do
  let payload ← (← check source).closedPayload
  let inputs ← ZkcTools.StructuredSource.inputs payload.entry.inputs json
  let (some abstract, _) ← (Bounds.closed payload (Bounds.values inputs)).mapError
    (Bounds.Failure.code false) | return false
  match closedOutcome (payload.denote Scalar Scalar inputs) with
  | .returned actual => return containsValues abstract (Bounds.values actual)
  | .stopped _ => return false

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let equal (name : String) (actual : Except String Json) (expected : Json) : IO Unit := do
    test (name ++ ": " ++ (match actual with | .error e => e | .ok _ => "returned"))
      (match actual with | .ok x => x == expected | _ => false)
  let refusal (name code : String) (actual : Except String Json) : IO Unit := do
    test (name ++ ": " ++ (match actual with | .error e => e | .ok _ => "returned"))
      (match actual with | .error x => x == code | _ => false)
  let rawRefusal (name : String) (actual : Except Failure (Result × Meter)) (code : Failure) : IO Unit :=
    test name (match actual with | .error x => x == code | _ => false)

  equal "max constant returned" (runClosed (constantProgram maximum)) (returned [index maximum])
  equal "max constant open" (runOpen (constantProgram maximum))
    (arr [.str "zkc.structured-open-result/0", arr [.str "returned", arr [.str (toString maximum)]],
      arr [], toJson (0 : Nat)])
  refusal "generated huge empty loop" "structured-evaluation-work-limit" (runClosed (generatedLoop maximum))
  refusal "generated huge open loop" "structured-open-work-limit" (runOpen (generatedLoop maximum))
  equal "zero loop" (runClosed (generatedLoop 0)) (returned [])
  equal "equal max endpoints allocate no range" (runClosed (generatedLoop maximum maximum)) (returned [])
  equal "reversed endpoints" (runClosed (generatedLoop 2 9)) (returned [])
  equal "ordinary empty body" (runClosed (generatedLoop 32)) (returned [])
  rawRefusal "raw empty body still charged" (raw (rawLoop 0 maximum)) .work
  rawRefusal "nested expansion analysis capacity" (raw (rawLoop 0 1000 (rawLoop 0 1000))) .analysis

  let untaken := program constants [] [] (.block [
    .instruction (.booleanConstant false) [] [.boolean] [] "condition",
    .instruction .branch [0] [] [
      .region [] [] (.block [constant maximum, constant 0, emptyLoop 0 1] (.yield [])),
      .region [] [] (.block [] (.yield []))] "branch"] (.ret []))
  equal "known false skips enormous branch" (runClosed untaken) (returned [])
  let uncertainBranch : RawRegion Ty Op := .letOp (.branch [] []) [0] []
    (.cons [] [] (rawLoop 0 maximum) (.cons [] [] (.ret []) .nil)) (.ret [])
  rawRefusal "unknown branch must still inspect costly arm"
    (raw uncertainBranch [.boolean none]) .work
  let oppositeBranch : RawRegion Ty Op := .letOp (.branch [] []) [0] []
    (.cons [] [] (.ret []) (.cons [] [] (rawLoop 0 maximum) .nil)) (.ret [])
  test "known true skips enormous false arm"
    (match raw oppositeBranch [.boolean (some true)] with | .ok (some [], _) => true | _ => false)
  let guardedSuffix : RawRegion Ty Op := .letOp (.branch [] []) [0] []
    (.cons [] [] (.ret []) (.cons [] [] (.stop .reject) .nil)) (rawLoop 0 maximum)
  test "known branch stop prevents enormous suffix"
    (match raw guardedSuffix [.boolean (some false)] with | .ok (none, _) => true | _ => false)
  rawRefusal "optional branch stop retains skipped-operation suffix"
    (raw guardedSuffix [.optional (.boolean (some false))]) .work
  let selected : RawRegion Ty Op := .letOp (.select .index) [0, 1, 2] [.index] .nil (.ret [0])
  for condition in [true, false] do
    test s!"known select chooses exact value {condition}"
      (match raw selected [.boolean (some condition), .index (exact 3), .index (exact maximum)] with
        | .ok (some [.index n], _) => n == exact (if condition then 3 else maximum)
        | _ => false)
  test "unknown select joins both values"
    (match raw selected [.boolean none, .index (exact 3), .index (exact maximum)] with
      | .ok (some [.index n], _) => n.lower == 3 && n.upper == maximum
      | _ => false)
  test "optional select retains absence after pruning"
    (match raw selected [.optional (.boolean (some true)), .index (exact 3), .index (exact maximum)] with
      | .ok (some [.optional (.index n)], _) => n == exact 3
      | _ => false)
  test "select keeps strict presence of the unselected operand"
    (match raw selected [.boolean (some true), .index (exact 3), .optional (.index (exact maximum))] with
      | .ok (some [.optional (.index n)], _) => n == exact 3
      | _ => false)
  let conditional := program constants [] [] (.block [constant maximum, constant 0,
    .instruction .loopCondition [0, 1] [] [.region [.index] [.boolean]
      (.block [.instruction (.booleanConstant false) [] [.boolean] [] "false"] (.condition [0]))]
      "conditional"] (.ret []))
  refusal "conditional early termination still allocates" "structured-evaluation-work-limit"
    (runClosed conditional)

  equal "append 4095 to 4096" (runClosed appendProgram [vector 4095, field 0]) (returned [vector 4096])
  refusal "append 4096 to 4097" "structured-evaluation-value-limit"
    (runClosed appendProgram [vector 4096, field 0])
  refusal "open generated result vector cap" "structured-open-value-limit"
    (runOpen appendProgram [arr (List.replicate 4096 (.str "0")), .str "0"])
  equal "repeated append length controls loop" (runClosed growingProgram [vector 0, field 0, index 12])
    (returned [index 12])
  equal "append boundary followed by length loop" (runClosed growingProgram [vector 4095, field 0, index 1])
    (returned [index 4096])
  refusal "carried append exceeds capacity" "structured-evaluation-value-limit"
    (runClosed growingProgram [vector 4095, field 0, index 2])

  for (name, contract, a, b) in [
      ("index_add", "index.add", maximum, 1), ("index_mul", "index.mul", maximum, 2),
      ("index_sub", "index.sub", 0, 1), ("index_div", "index.div", 2, 0),
      ("index_mod", "index.mod", 2, 0)] do
    let source := program [binding "arithmetic" contract] [.index, .index] [.index]
      (.block [exec name "arithmetic" [0, 1] [.index]] (.ret [0]))
    equal (name ++ " actual semantic refusal") (runClosed source [index a, index b])
      (arr [.str "stopped", .str "refused"])

  let multiply := program (constants ++ [binding "multiply" "index.mul"]) [] []
    (.block [constant 1000000, constant 1000000,
      exec "index_mul" "multiply" [0, 1] [.index], constant 0, emptyLoop 0 1] (.ret []))
  refusal "generated multiplied bound" "structured-evaluation-work-limit" (runClosed multiply)
  let doubling := program (constants ++ [binding "multiply" "index.mul"]) [] []
    (.block [constant 1, constant 30, constant 0,
      .instruction .loop [0, 1, 2] [.index] [.region [.index, .index] [.index]
        (.block [constant 2, exec "index_mul" "multiply" [0, 2] [.index]] (.yield [0]))] "double",
      emptyLoop 1 0] (.ret []))
  refusal "loop-generated exponential bound" "structured-evaluation-work-limit" (runClosed doubling)

  let captured := program [binding "multiply" "index.mul", binding "constant" "index.constant"]
    [.index, .index, .index] [.index] (.block [constant 0,
      .instruction .loop [0, 3, 1, 2] [.index] [.region [.index, .index, .index] [.index, .index]
        (.block [exec "index_mul" "multiply" [1, 2] [.index]] (.yield [0, 3]))] "multiply",
      emptyLoop 1 0] (.ret [0]))
  equal "captured versus carried state order" (runClosed captured [index 2, index 10, index 3])
    (returned [index 2000])

  let folded := { program [binding "append" "vector.append" true]
    [vectorTy, vectorTy, .boolean] [vectorTy]
    (.block [.instruction (.apply "fold") [0, 1, 2] [vectorTy] [] "fold.call"] (.ret [0]))
    [helper "step" [vectorTy, fieldTy, vectorTy, .boolean] [vectorTy]
      (.block [exec "vector_append" "append" [0, 1] [vectorTy]] (.ret [0])),
     helper "predicate" [fieldTy, vectorTy, .boolean] [.boolean] (.block [] (.ret [2])),
     .finite ⟨"fold", .privateDef, [vectorTy, vectorTy, .boolean], [vectorTy],
       "elements", "step", "predicate"⟩]
    with domains := [⟨"elements", [vectorTy], [.elements 0], 0⟩] }
  equal "fold step receives state item arguments captures"
    (runClosed folded [vector 1, vector 4095, arr [.str "bool", .bool true]]) (returned [vector 4096])
  refusal "fold-generated vector length" "structured-evaluation-value-limit"
    (runClosed folded [vector 2, vector 4095, arr [.str "bool", .bool true]])
  equal "false fold predicate preserves state"
    (runClosed folded [vector 2, vector 4096, arr [.str "bool", .bool false]]) (returned [vector 4096])
  equal "empty domain does not call step"
    (runClosed folded [vector 0, vector 4096, arr [.str "bool", .bool true]]) (returned [vector 4096])

  let receiveIndex := arr [.str "receive", .str "bound", .str "V", .str "P", wireType .index]
  let reply (request value : Json) := arr [.str "reply", request, arr [.str "value", value]]
  let receivedLoop : Snapshot := (let contractDefinitions : List Definition := [helper "work" [.index] [.index] (.block [constant 0, emptyLoop 0 1] (.ret [1])),
     .function ⟨"main", .protocol, .publicDef, [.index], [.index],
       some ⟨["P", "V"], [["V"]], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
       .block [.instruction (.exchange "V" "P") [0] [.index] [] "bound",
         .instruction (.localCall "work" "P") [0] [.index] [] "work"] (.ret [0])⟩]
   ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'),
    "main", [], [], constants, contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
  let receiveRun (replies : List Json) : Except String Json := do
    evaluateOpen (← check receivedLoop) (openRequest [.null] replies)
  test "received small index executes independently"
    (hasOpenReturn (receiveRun [reply receiveIndex (.str "2")]) [.str "2"])
  refusal "dynamic received index" "structured-open-work-limit"
    (receiveRun [reply receiveIndex (.str (toString maximum))])
  refusal "unused typed reply suffix policy" "structured-open-work-limit"
    (receiveRun [reply receiveIndex (.str "2"), reply receiveIndex (.str (toString maximum))])

  let receiveVector := arr [.str "receive", .str "vector", .str "V", .str "P", wireType vectorTy]
  let receivedAppend : Snapshot := (let contractDefinitions : List Definition := [helper "work" [vectorTy, fieldTy] [vectorTy]
       (.block [exec "vector_append" "append" [0, 1] [vectorTy]] (.ret [0])),
     .function ⟨"main", .protocol, .publicDef, [vectorTy, fieldTy], [vectorTy],
       some ⟨["P", "V"], [["V"], ["P"]], [["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
       .block [.instruction (.exchange "V" "P") [0] [vectorTy] [] "vector",
         .instruction (.localCall "work" "P") [0, 2] [vectorTy] [] "work"] (.ret [0])⟩]
   ⟨receivedLoop.source, "main", [], [],
    [binding "append" "vector.append" true], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
  let receivedAppendRun (n : Nat) : Except String Json := do
    evaluateOpen (← check receivedAppend) (openRequest [.null, .str "0"]
      [reply receiveVector (arr (List.replicate n (.str "0")))])
  test "received 4095 append executes" (hasOpenReturn (receivedAppendRun 4095)
    [arr (List.replicate 4096 (.str "0"))])
  refusal "received vector-generated length cap" "structured-open-value-limit" (receivedAppendRun 4096)

  let optionalCall (n : Nat) : Snapshot := (let contractDefinitions : List Definition := [.function ⟨"ignored", .math, .privateDef, [.index], [.index], none, [], none,
       .block [.instruction (.indexConstant (toString n)) [] [.index] [] ""] (.ret [0])⟩,
     helper "work" [.index] [] (.block [constant 0, emptyLoop 0 1] (.ret [])),
     .function ⟨"main", .protocol, .publicDef, [.index], [],
       some ⟨["P"], [["P"]], []⟩, [], some (.protocol ⟨"main", []⟩),
       .block [.instruction (.call "ignored") [0] [.index] [] "",
         .instruction (.localCall "work" "P") [0] [] [] "work"] (.ret [])⟩]
   ⟨receivedLoop.source, "main", [], [], constants, contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
  equal "math helper retains optional dependency precision" (runOpen (optionalCall 2) [.null])
    (arr [.str "zkc.structured-open-result/0", arr [.str "returned", arr []], arr [], toJson (0 : Nat)])
  refusal "math helper with absent unused operand can generate huge bound"
    "structured-open-work-limit" (runOpen (optionalCall maximum) [.null])

  -- A known small index must stay independent of an unrelated large vector.
  let separate := program constants [vectorTy, .index] [vectorTy]
    (.block [constant 0, emptyLoop 0 2] (.ret [1]))
  equal "large vector unrelated to loop count" (runClosed separate [vector 4096, index 12])
    (returned [vector 4096])
  let manyOutputs := program [] [vectorTy] (List.replicate 64 vectorTy)
    (.block [] (.ret (List.replicate 64 0)))
  refusal "aliased output traversal is charged" "structured-evaluation-work-limit"
    (runClosed manyOutputs [vector 4096])

  let expensive := RawRegion.letOp (.exec (.vectorSum scalarDomain)) [1] [fieldTy] .nil (.ret [2])
  let repeated := RawRegion.letOp (.loop [] [vectorTy]) [0, 1, 2] []
    (.cons [.index, vectorTy] [vectorTy] expensive .nil) (.ret [])
  rawRefusal "vector sum work" (raw repeated
    [.index (exact 0), .index (exact 100), .vector (exact 4096)]) .work
  for primitive in [Primitive.vectorLength scalarDomain, .vectorSplit scalarDomain,
      .vectorAppend scalarDomain, .vectorEqual scalarDomain] do
    let args := match primitive with
      | .vectorAppend _ => [Value.vector (exact 4095), .atom]
      | .vectorEqual _ => [.vector (exact 4096), .vector (exact 4096)]
      | _ => [.vector (exact 4096)]
    test ("linear vector work: " ++ reprStr primitive)
      (match (Bounds.primitive primitive args).run {} with
        | .ok (_, meter) => meter.work ≥ 4096
        | _ => false)
  rawRefusal "unknown operands are capacity errors" (raw (.ret [1])) .unknown
  rawRefusal "empty context cannot alias zero" (raw (.ret [0])) .unknown
  rawRefusal "context size is an invalid index"
    (raw (.ret [1]) [.index (exact 7)]) .unknown
  let lexical : RawRegion Ty Op := .bind [.index, .index]
    (.letOp (.indexConstant 19) [] [.index] .nil (.ret [0, 3]))
    (.ret [0, 1, 2, 3, 4])
  test "lexical results preserve order and caller context"
    (match raw lexical ([3, 7, 11].map (Value.index ∘ exact)) with
      | .ok (some result, _) => result == ([19, 11, 3, 7, 11].map (Value.index ∘ exact))
      | _ => false)
  -- Repeatedly select the original input through an expanding SSA context.
  -- This is the maintained maximum-instruction regression, independent of
  -- the concrete interpreter and of the policy's individual charge constants.
  let oldInput (n : Nat) : RawRegion Ty Op := (List.range n).foldr
    (fun index next => .letOp .booleanXor [index, index] [.boolean] .nil next) (.ret [n])
  let smaller := raw (oldInput 2048) [.boolean (some true)]
  let larger := raw (oldInput 4096) [.boolean (some true)]
  test "maximum instruction context preserves the original input"
    (match larger with | .ok (some [.boolean (some true)], _) => true | _ => false)
  test "SSA analysis grows linearly with instruction count"
    (match smaller, larger with
      | .ok (_, a), .ok (_, b) => b.analysis ≤ 3 * a.analysis && b.work ≤ 3 * a.work
      | _, _ => false)
  let longName := String.ofList (List.replicate 240 'a')
  let analysisHeavy := program constants [] [] (.block [constant 0, constant 3000,
    .instruction .loop [1, 0] [] [.region [.index] []
      (.block [.instruction (.apply longName) [] [] [] "callback"] (.yield []))] "loop"] (.ret []))
    [helper longName [] [] (.block [] (.ret []))]
  refusal "actual helper expansion analysis capacity" "structured-bounds-analysis-limit"
    (runClosed analysisHeavy)

  let helperPrefix := String.ofList (List.replicate 64 'h')
  let lateName := helperPrefix ++ "125"
  let lateHelpers := (List.range 125).map (fun n =>
    helper (helperPrefix ++ toString n) [] [] (.block [] (.ret []))) ++
    [helper lateName [.index] [.index]
      (.block [constant 1, exec "index_add" "add" [0, 1] [.index]] (.ret [0]))]
  let lateLoop := program (constants ++ [binding "add" "index.add"]) [] [.index]
    (.block [constant 0, constant 512,
      .instruction .loop [1, 0, 1] [.index] [.region [.index, .index] [.index]
        (.block [.instruction (.apply lateName) [1] [.index] [] "late"] (.yield [0]))] "loop"]
      (.ret [0])) lateHelpers
  test "late-helper control uses maximum definition count" (lateLoop.definitions.length == 128)
  equal "late helper in 128-definition unit executes 512 iterations"
    (runClosed lateLoop) (returned [index 512])
  -- The name index must not turn a name-only match into authority.
  let identities : Except String Bool := do
    let payload ← (← check lateLoop).closedPayload
    let .ok (table, _) := (prepareHelpers payload.definitions).run {} | return false
    let genuine : Helper := ⟨lateName, .local, [.index], [.index]⟩
    let invalid := [{ genuine with kind := .math },
      { genuine with inputs := [.boolean] }, { genuine with outputs := [.boolean] },
      { genuine with name := "missing" }]
    return invalid.all fun identity => match (findHelper table identity).run {} with
      | .error .unknown => true
      | _ => false
  test "helper lookup refuses kind input output and name mismatches" (identities == .ok true)

  -- Generated arithmetic, known-Boolean branches, append and carried loops.
  -- Successful returns must be contained, so refusal cannot pass this check.
  let arithmetic := program (constants ++ [binding "add" "index.add", binding "mul" "index.mul",
      binding "div" "index.div", binding "mod" "index.mod", binding "equal" "index.equal"])
    [.index, .index] [.index, .index, .boolean]
    (.block [exec "index_add" "add" [0, 1] [.index], constant 3,
      exec "index_mul" "mul" [0, 1] [.index], constant 2,
      exec "index_div" "div" [1, 0] [.index], exec "index_mod" "mod" [2, 1] [.index],
      exec "index_equal" "equal" [0, 0] [.boolean]] (.ret [2, 1, 0]))
  let branchClient := program (constants ++ [binding "equal" "index.equal"])
    [.boolean] [.index, .boolean]
    (.block [.instruction .branch [0] [.index]
      [.region [] [.index] (.block [constant 7] (.yield [0])),
       .region [] [.index] (.block [constant 23] (.yield [0]))] "choose", constant 7,
      exec "index_equal" "equal" [0, 1] [.boolean]] (.ret [2, 0]))
  let unknownBranchClient := program (constants ++ [binding "equal" "index.equal",
      binding "field_equal" "field.equal" true]) [fieldTy, fieldTy] [.index, .boolean]
    (.block [exec "field_equal" "field_equal" [0, 1] [.boolean],
      .instruction .branch [0] [.index]
      [.region [] [.index] (.block [constant 7] (.yield [0])),
       .region [] [.index] (.block [constant 23] (.yield [0]))] "choose", constant 7,
      exec "index_equal" "equal" [0, 1] [.boolean]] (.ret [2, 0]))
  for (label, source, arguments) in [
      ("arithmetic-zero", arithmetic, [index 0, index 0]),
      ("arithmetic-generated", arithmetic, [index 11, index 7]),
      ("arithmetic-large", arithmetic, [index (maximum / 16), index 7]),
      ("branch-true", branchClient, [arr [.str "bool", .bool true]]),
      ("branch-false", branchClient, [arr [.str "bool", .bool false]]),
      ("unknown-branch-true", unknownBranchClient, [field 5, field 5]),
      ("unknown-branch-false", unknownBranchClient, [field 5, field 7]),
      ("append-empty", appendProgram, [vector 0, field 9]),
      ("append-boundary", appendProgram, [vector 4095, field 9]),
      ("loop-zero", growingProgram, [vector 3, field 9, index 0]),
      ("loop-growth", growingProgram, [vector 3, field 9, index 12]),
      ("late-helper-loop", lateLoop, [])] do
    let contained := containsReturn source arguments
    test ("concrete return contained: " ++ label ++ ": " ++ reprStr contained) (contained == .ok true)
  test "containment check detects an incorrect index bound"
    (!containsValue (.index (exact 2)) (.index (exact 3)))
  test "containment check detects incorrect length and known boolean"
    (!containsValue (.vector (exact 2)) (.vector (exact 3)) &&
     !containsValue (.boolean (some false)) (.boolean (some true)))

  -- Optional guards must not prune the absent path that reaches a large loop.
  let optionalGuard := RawRegion.letOp .guard [0] [] .nil (rawLoop 0 maximum)
  rawRefusal "possibly absent false guard retains continuation"
    (raw optionalGuard [.optional (.boolean (some false))]) .work
  test "definitely false guard stops before large suffix"
    (match raw optionalGuard [.boolean (some false)] with | .ok (none, _) => true | _ => false)

  let constantMap := mapProgram [true, true, false] constantFormula
  let .ok constantPayload := (do (← check constantMap).closedPayload) |
    throw (IO.userError "constant map must be admitted")
  let .ok (mapHelpers, _) := (prepareHelpers constantPayload.definitions).run {} |
    throw (IO.userError "constant map helper index must be prepared")
  let mapSpec : MapSpec := ⟨"formula", scalarDomain, [true, true, false]⟩
  let analyzeMap (args : Env) := (operation mapHelpers (.map mapSpec) args .nil).run {}
  let mapArgs (n : Nat) : Env := [.vector (exact n), .vector (exact n), .atom]
  for n in [0, 1, 65, 4096] do
    equal s!"constant map returns every row {n}"
      (runClosed constantMap [vector n, vector n, field 23])
      (returned [vectorValues (List.replicate n 7)])
    test s!"map output length contains successful return {n}"
      (containsReturn constantMap [vector n, vector n, field 23] == .ok true)
  refusal "map input 4097 is refused at unchanged decoder boundary" "structured-list-limit"
    (runClosed constantMap [vector 4097, vector 4097, field 23])
  rawRefusal "map cannot construct a 4097-element vector" (analyzeMap (mapArgs 4097)) .value
  for (left, right) in [(2, 1), (0, 1), (1, 0), (4096, 4095)] do
    equal s!"constant map checks unused row mismatch {left}/{right}"
      (runClosed constantMap [vector left, vector right, field 23])
      (arr [.str "stopped", .str "refused"])
  let wideMap := mapProgram (List.replicate 64 true) (.block [] (.ret [0]))
  equal "aggregate 64 by 65 row tuple work exceeds vector cap but fits work budget"
    (runClosed wideMap (List.replicate 64 (vector 65))) (returned [vector 65])

  let orderedMap := mapProgram [false, true, false, true, false]
    (.block [.instruction (.fieldSubtract scalarDomain) [0, 1] [fieldTy] [] "",
      .instruction (.fieldSubtract scalarDomain) [3, 4] [fieldTy] [] "",
      .instruction (.fieldMultiply scalarDomain) [0, 6] [fieldTy] [] "",
      .instruction (.fieldAdd scalarDomain) [2, 0] [fieldTy] [] ""] (.ret [0]))
  let orderedInputs := [field 20, vectorValues [1, 2], field 10, vectorValues [3, 4], field 5]
  equal "broadcasts retain original positional scalar tuple"
    (runClosed orderedMap orderedInputs) (returned [vectorValues [54, 48]])
  test "mixed broadcast output is contained" (containsReturn orderedMap orderedInputs == .ok true)

  -- Scalar helper analysis is repeated logically, not traversed once per row.
  let one := analyzeMap (mapArgs 1)
  let many := analyzeMap (mapArgs 4096)
  test "map analysis does not repeat identical helper traversal per row"
    (match one, many with
      | .ok (_, a), .ok (some [.vector n], b) =>
          n == exact 4096 && a.analysis == b.analysis && b.work > 4096 * a.work / 2
      | _, _ => false)
  let costlyMap := mapProgram [true] (repeatedFormula 100)
  equal "nonempty map below aggregate work limit executes helper"
    (runClosed costlyMap [vector 65]) (returned [vector 65])
  refusal "map reserves every potential helper invocation" "structured-evaluation-work-limit"
    (runClosed costlyMap [vector 4096])
  equal "empty map skips otherwise excessive helper expansion"
    (runClosed costlyMap [vector 0]) (returned [vector 0])
  let costlyUnused := mapProgram [true, true] (repeatedFormula 100)
  equal "mismatch skips otherwise excessive helper expansion"
    (runClosed costlyUnused [vector 4096, vector 4095]) (arr [.str "stopped", .str "refused"])

  let nestedMap := mapProgram [true]
    (.block [.instruction (.call "pair") [0] [fieldTy, fieldTy] [] "",
      .instruction (.call "discard") [2] [] [] "",
      .instruction (.fieldAdd scalarDomain) [0, 1] [fieldTy] [] ""] (.ret [0]))
    [mathHelper "pair" [fieldTy] [fieldTy, fieldTy] (.block [] (.ret [0, 0])),
     mathHelper "discard" [fieldTy] [] (.block [] (.ret []))]
  equal "nested scalar helpers preserve multiple and zero results"
    (runClosed nestedMap [vectorValues [3, 8]]) (returned [vectorValues [6, 16]])
  test "nested scalar helper result is contained"
    (containsReturn nestedMap [vectorValues [3, 8]] == .ok true)
  let nestedCostly := mapProgram [true]
    (.block [.instruction (.call "discard") [0] [] [] ""] (.ret [0]))
    [mathHelper "discard" [fieldTy] []
      (.block (List.replicate 100
        (.instruction (.fieldAdd scalarDomain) [0, 0] [fieldTy] [] "")) (.ret []))]
  refusal "discarded nested helper work is multiplied" "structured-evaluation-work-limit"
    (runClosed nestedCostly [vector 4096])

  test "map absence stops before helper or huge continuation"
    (match (region (operation mapHelpers)
        (.letOp (.map mapSpec) [0, 1, 2] [vectorTy] .nil (rawLoop 0 maximum))
        [.vector (exact 0), .vector (exact 0), .absent]).run {} with
      | .ok (none, _) => true | _ => false)
  test "optional map returns only the present path"
    (match analyzeMap [.optional (.vector (exact 2)), .vector (exact 2), .atom] with
      | .ok (some [.vector n], _) => n == exact 2 | _ => false)
  test "optional map mismatch cannot reach the continuation"
    (match (region (operation mapHelpers)
        (.letOp (.map mapSpec) [0, 1, 2] [vectorTy] .nil (rawLoop 0 maximum))
        [.optional (.vector (exact 0)), .vector (exact 1), .atom]).run {} with
      | .ok (none, _) => true | _ => false)
  for args in [[arr [], arr [], .null], [arr [.str "0"], .null, .str "23"]] do
    equal "owned Local map call requires even unused inputs" (runOpen constantMap args)
      (arr [.str "zkc.structured-open-result/0", arr [.str "stopped", .str "incomplete", .str "work"],
        arr [arr [.str "stop", .str "incomplete", .str "work", toJson (0 : Nat)]], toJson (0 : Nat)])
  test "nonowner map wrapper skips helper and returns absent"
    (match (Bounds.protocolOperation mapHelpers [] {} 1 (fun _ => pure none)
        (.localCall ⟨"work", .local, mapSpec.arguments, [vectorTy]⟩ rfl 0 "work")
        [.absent, .absent, .absent] .nil).run {} with
      | .ok (some [.absent], _) => true | _ => false)
  test "Local invoke absent-output boundary remains distinct from direct map"
    (match (operation mapHelpers
        (.invoke ⟨"mapping", .local, mapSpec.arguments, [vectorTy]⟩)
        [.absent, .absent, .absent] .nil).run {} with
      | .ok (some [.absent], _) => true | _ => false)
  rawRefusal "optional Local invoke mismatch retains skipped-call continuation"
    ((region (operation mapHelpers)
        (.letOp (.invoke ⟨"mapping", .local, mapSpec.arguments, [vectorTy]⟩)
          [0, 1, 2] [vectorTy] .nil (rawLoop 0 maximum))
        [.optional (.vector (exact 0)), .vector (exact 1), .atom]).run {}) .work

  test "uncertain shapes retain every potentially successful common length"
    (match analyzeMap [.vector ⟨0, 9⟩, .vector ⟨3, 12⟩, .atom] with
      | .ok (some [.vector n], _) => n == ⟨3, 9⟩ | _ => false)
  test "unknown row can agree with empty only at zero"
    (match analyzeMap [.vector (exact 0), .vector ⟨0, 9⟩, .atom] with
      | .ok (some [.vector n], _) => n == exact 0 | _ => false)
  test "disjoint shape intervals cannot return"
    (match analyzeMap [.vector ⟨0, 2⟩, .vector ⟨3, 9⟩, .atom] with
      | .ok (none, _) => true | _ => false)
  rawRefusal "row shape must remain a vector"
    (analyzeMap [.atom, .vector (exact 2), .atom]) .unknown
  rawRefusal "map broadcast must remain scalar"
    (analyzeMap [.vector (exact 2), .vector (exact 2), .vector (exact 2)]) .unknown
  rawRefusal "map requires full original tuple arity"
    (analyzeMap [.vector (exact 2), .vector (exact 2)]) .unknown
  for spec in [{mapSpec with helperName := "missing"},
      {mapSpec with field := "other-field"}, {mapSpec with rowwise := [true]}] do
    let args := if spec.rowwise.length == 1 then [Value.vector (exact 1)] else mapArgs 1
    rawRefusal "map checks full helper identity"
      ((operation mapHelpers (.map spec) args .nil).run {}) .unknown
  rawRefusal "nonempty map cannot use a Local helper as Math"
    ((operation mapHelpers (.map {mapSpec with helperName := "mapping"}) (mapArgs 1) .nil).run {})
    .unknown
  test "empty rows do not require dynamic helper invocation"
    (match (operation {} (.map mapSpec) (mapArgs 0) .nil).run {} with
      | .ok (some [.vector n], _) => n == exact 0 | _ => false)
  test "known mismatch does not require dynamic helper invocation"
    (match (operation {} (.map mapSpec)
        [.vector (exact 0), .vector (exact 1), .atom] .nil).run {} with
      | .ok (none, _) => true | _ => false)
  rawRefusal "unknown nonempty shape still checks helper body"
    ((operation {} (.map mapSpec) [.vector ⟨0, 1⟩, .vector ⟨0, 1⟩, .atom] .nil).run {}) .unknown
  test "shape mismatch still charges every collected row length"
    (match (operation {} (.map ⟨"missing", scalarDomain, [true, true, true]⟩)
        [.vector (exact 0), .vector (exact 1), .vector (exact 4096)] .nil).run {} with
      | .ok (none, meter) => meter.work ≥ 4096 | _ => false)
  test "aggregate work can exceed vector capacity"
    (match (chargeRepeated 64 65).run {} with | .ok (_, meter) => meter.work == 4160 | _ => false)
  test "zero repeated work does not overflow multiplication"
    (match (chargeRepeated maximum 0).run {} with | .ok (_, meter) => meter.work == 0 | _ => false)
  test "aggregate repeated work stops at remaining work budget"
    (match (chargeRepeated maximum maximum).run {} with | .error .work => true | _ => false)

  let failed ← failures.get
  unless failed.isEmpty do
    throw (IO.userError (String.intercalate "\n" failed.reverse))
  IO.println s!"Structured bounds controls passed ({← count.get})"

#eval run
end Tests.StructuredBounds
