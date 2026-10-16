import Zkc.Source.Structured.Import
import Zkc.Source.Structured.Component
import Zkc.Source.Structured.MapLaws
import Mathlib.Data.ZMod.Basic

/-! Independent retained-declaration controls. Authored constructor subjects
exercise full-unit admission; they are not claimed to be native source captures. -/

open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredMaps

private abbrev scalar : Ty := .field scalarDomain
private abbrev vector : Ty := .vector scalarDomain
private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def root : Definition := .function ⟨"main", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], none, .block [] (.ret [])⟩
private def snapshot (definitions : List Definition) : Snapshot :=
  (let contractDefinitions : List Definition := root :: definitions
   ⟨digest, "main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none)⟩)
private def admits (definitions : List Definition) : Bool := (check (snapshot definitions)).isOk

-- Isolate the availability boundary: complete admission now also checks the
-- same combined reference depth earlier, while ordering checked protocols.
private def availabilityPhase (unit : Snapshot) : Except String Unit := do
  let (domains, headers, summaries) ← checkUnitHeaders unit
  let helpers ← checkUnitHelpers unit domains summaries
  let protocols ← unit.protocolFunctions.mapM fun function =>
    checkProtocol unit domains summaries function headers
  checkUnitAvailability (helpers.map (·.definition)) protocols

private def math (name : String) (inputs outputs : List Ty)
    (instructions : List Instruction := []) (returns : List Nat := []) : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none,
    .block instructions (.ret returns)⟩
private def identity : Definition := math "scalar" [scalar, scalar] [scalar] [] [0]
private def mapDeclaration : MapDeclaration :=
  ⟨"mapped", [vector, scalar], [vector], "scalar", [true, false]⟩
private def realization : RealizationDeclaration :=
  ⟨"realized", [scalar, scalar], [scalar], "scalar"⟩
private def arr (values : List Json) : Json := .arr values.toArray
private def typeWire : Ty → Json
  | .boolean => arr [.str "bool"]
  | .index => arr [.str "index"]
  | .field domain => arr [.str "field", .str domain]
  | .vector domain => arr [.str "vector", .str domain]
  | .group domain => arr [.str "group", .str domain]
  | .service contract => arr [.str "service", .str contract]
private def mapWire (mask : List Json) : Json := arr [
  .str "map", .str "mapped", arr (mapDeclaration.inputs.map typeWire),
  arr (mapDeclaration.outputs.map typeWire), .str "scalar", arr mask]
private def invokeInstruction (name : String) (inputs : List Nat) (outputs : List Ty) : Instruction :=
  .instruction (.call name) inputs outputs [] ""
private def localApply (name target : String) (inputs outputs : List Ty) : Definition :=
  .function ⟨name, .local, .privateDef, inputs, outputs, none, [], some (name, []),
    .block [.instruction (.apply target) (List.range inputs.length) outputs [] "apply"]
      (.ret (List.range outputs.length))⟩
private def localCall (target : String) (inputs outputs : List Ty) : Definition :=
  .function ⟨"other", .protocol, .publicDef, inputs, outputs,
    some ⟨["P"], inputs.map (fun _ => ["P"]), outputs.map (fun _ => ["P"])⟩,
    [], none, .block [.instruction (.localCall target "P")
      (List.range inputs.length) outputs [] "call"] (.ret (List.range outputs.length))⟩

private abbrev F := ZMod 97
private def spec : MapSpec := ⟨"scalar", scalarDomain, [true, false]⟩
private def table : Meanings F F := [⟨spec.helper,
  fun values => .done (.cons (values.get .here + values.get (.there .here)) .nil)⟩]

-- Logical u64 length boundaries are checked without constructing giant vectors.
example : Evaluation.mapShape [indexLimit - 1] = .returned (indexLimit - 1) := by decide +kernel
example : Evaluation.mapShape [indexLimit] = .stopped .exhausted := by decide +kernel
example : Evaluation.mapShape [0, 1, indexLimit] = .stopped .refused := by decide +kernel
example : Evaluation.mapShape [0, indexLimit, 1] = .stopped .exhausted := by decide +kernel

-- A missing helper is unreachable for zero rows, but is observed on the first row.
example : Evaluation.denoteMap (F := F) (G := F) (I := closedInterface) [] spec
    (.cons [] (.cons (8 : F) .nil)) = .done (.cons [] .nil) := rfl
example : Evaluation.denoteMap (F := F) (G := F) (I := closedInterface) [] spec
    (.cons [1] (.cons (8 : F) .nil)) = .halt .refused := rfl

-- Direct optional map is strict even if the absent broadcast would be unused.
example : Evaluation.componentOperation (F := F) (G := F) SiteObservations.closed
    ⟨table, []⟩ (.map spec) (.cons (some []) (.cons none .nil)) .nil = .halt .incomplete := rfl

-- An invalid unused row is checked even when the first, live row is empty.
example : Evaluation.denoteMap (F := Nat) (G := Nat) (I := closedInterface) []
    ⟨"never-reached", scalarDomain, [true, true, false]⟩
    (.cons [] (.cons [1] (.cons (9 : Nat) .nil))) = .halt .refused := rfl

-- Scalar broadcasts are retained between row operands, without permutation.
example : Evaluation.mapRowArguments (F := Nat) (G := Nat) scalarDomain
    [false, true, false, true, true, false]
    (.cons (2 : Nat) (.cons [3, 5] (.cons (7 : Nat) (.cons [11, 13] (.cons [17, 19] (.cons (23 : Nat) .nil)))))) 1 =
      some (.cons 2 (.cons 5 (.cons 7 (.cons 13 (.cons 19 (.cons 23 .nil)))))) := rfl

private def wrongIdentity : Meanings F F := [⟨{spec.helper with name := "other"},
  fun _ => .done (.cons 0 .nil)⟩]
example : Evaluation.denoteMap wrongIdentity spec (.cons [1] (.cons (8 : F) .nil)) = .halt .refused := rfl

private def rowInterface : PIR.Signature := ⟨Nat, fun _ => Unit⟩
private def effectfulRow (index : Nat) : PIR.Proc rowInterface Nat :=
  .call index (fun _ => if index = 1 then .halt .reject else .done index)
example : Evaluation.mapRows effectfulRow [0, 1, 2] =
    .call (0 : Nat) (fun _ => .call (1 : Nat) (fun _ => .halt .reject)) := rfl

private def zeroHelper : Helper := ⟨"zero", .math, [], []⟩
private def zeroCall : Region dialect [] [] :=
  .letOp (.invoke zeroHelper) .nil .nil (.ret .nil)
example : zeroCall.denote (meaning F F [⟨zeroHelper, fun _ => .halt .reject⟩]) Values.nil.get =
    .halt .reject := rfl

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  test "unused-map" (admits [identity, .map mapDeclaration])
  test "unused-realization" (admits [identity, .realization realization])
  test "strict-bool-wire" ((Format.definition (mapWire [.bool true, .bool false])).isOk)
  for bad in [toJson (1 : Nat), .str "true", .null, arr []] do
    test "wire-mask-not-bool" (!(Format.definition (mapWire [bad, .bool false])).isOk)
  test "mask-size" (!admits [identity, .map {mapDeclaration with rowwise := [true]}])
  test "mask-none" (!admits [identity, .map {mapDeclaration with rowwise := [false, false]}])
  test "mask-empty" (!admits [identity, .map {mapDeclaration with rowwise := []}])
  test "lifted-abi" (!admits [identity, .map {mapDeclaration with inputs := [scalar, vector]}])
  test "map-result-abi" (!admits [identity, .map {mapDeclaration with outputs := [scalar]}])
  test "map-root-zero-results" (!admits [math "scalar" [scalar, scalar] [], .map mapDeclaration])
  test "map-root-multiple-results" (!admits [math "scalar" [scalar, scalar] [scalar, scalar] [] [0, 1], .map mapDeclaration])
  test "map-helper-missing" (!admits [.map mapDeclaration])
  test "realization-full-abi" (!admits [identity, .realization {realization with outputs := [scalar, scalar]}])
  for name in ["", "1bad", "a/b", "a b", "é", String.ofList (List.replicate 129 'a')] do
    test "invalid-unused-map-name" (!admits [identity, .map {mapDeclaration with name}])
    test "invalid-unused-realize-name" (!admits [identity, .realization {realization with name}])
  for name in [String.ofList (List.replicate 128 'a'), "_A.0-b"] do
    test "preparation-name-boundary" (admits [identity, .map {mapDeclaration with name}])
  for size in [512, 513] do
    let helper := String.ofList (List.replicate size 'h')
    test "helper-name-wire-boundary" ((admits [math helper [scalar, scalar] [scalar] [] [0],
      .map {mapDeclaration with helper}]) == (size == 512))
  let fullABI := [vector, .index, .boolean, .group groupDomain, scalar]
  test "realize-full-projection-abi" (admits [math "all" fullABI fullABI [] (List.range fullABI.length),
    .realization ⟨"projection", fullABI, fullABI, "all"⟩])
  test "realize-zero-results" (admits [math "all" fullABI [],
    .realization ⟨"projection", fullABI, [], "all"⟩])
  let deadIndex := .instruction (.indexConstant "0") [] [.index] [] ""
  let indexMath := math "scalar" [scalar, scalar] [scalar] [deadIndex] [1]
  test "map-dead-index-forbidden" (!admits [indexMath, .map mapDeclaration])
  test "realize-pure-index-permitted" (admits [indexMath, .realization realization])
  let badLeaf := math "dead" [] [] [deadIndex]
  let deadCall := math "scalar" [scalar, scalar] [scalar] [invokeInstruction "dead" [] []] [0]
  test "map-dead-transitive-zero-call" (!admits [badLeaf, deadCall, .map mapDeclaration])
  test "realize-transitive-zero-call" (admits [badLeaf, deadCall, .realization realization])
  let zeroLeaf := math "zero" [scalar] []
  let tupleLeaf := math "tuple" [scalar, scalar] [scalar, scalar] [] [1, 0]
  let nested := math "scalar" [scalar, scalar] [scalar]
    [invokeInstruction "zero" [0] [], invokeInstruction "tuple" [0, 1] [scalar, scalar]] [0]
  test "map-zero-and-tuple-callees" (admits [zeroLeaf, tupleLeaf, nested, .map mapDeclaration])
  let cyclic := math "scalar" [scalar, scalar] [scalar]
    [invokeInstruction "scalar" [0, 1] [scalar]] [0]
  test "unused-map-cycle" (!admits [cyclic, .map mapDeclaration])
  test "unused-realize-cycle" (!admits [cyclic, .realization realization])
  test "apply-map" (admits [identity, .map mapDeclaration,
    localApply "wrapper" "mapped" [vector, scalar] [vector]])
  test "apply-realize" (admits [identity, .realization realization,
    localApply "wrapper" "realized" [scalar, scalar] [scalar]])
  test "protocol-map-forbidden" (!admits [identity, .map mapDeclaration,
    localCall "mapped" [vector, scalar] [vector]])
  test "protocol-realize-forbidden" (!admits [identity, .realization realization,
    localCall "realized" [scalar, scalar] [scalar]])
  test "math-call-map-forbidden" (!admits [identity, .map mapDeclaration,
    math "caller" [vector, scalar] [vector] [invokeInstruction "mapped" [0, 1] [vector]] [0]])
  test "math-call-realize-forbidden" (!admits [identity, .realization realization,
    math "caller" [scalar, scalar] [scalar] [invokeInstruction "realized" [0, 1] [scalar]] [0]])
  test "map-helper-realize-forbidden" (!admits [identity, .realization realization,
    .map {mapDeclaration with helper := "realized"}])
  test "realize-helper-map-forbidden" (!admits [identity, .map mapDeclaration,
    .realization ⟨"other", [vector, scalar], [vector], "mapped"⟩])
  test "duplicate-original-kinds" (!admits [identity, .map mapDeclaration,
    .realization {realization with name := "mapped"}])
  test "finite-callback-map-forbidden" (!(Definition.map mapDeclaration).acceptsEdge (.callback .local))
  test "finite-callback-realization-forbidden" (!(Definition.realization realization).acceptsEdge (.callback .local))
  test "protocol-finite-forbidden"
    (!(Definition.finite ⟨"finite", .privateDef, [], [], "d", "step", ""⟩).acceptsEdge .localCall)
  let domain : Domain := ⟨"elements", [vector], .elements 0⟩
  let step := math "step" [scalar, scalar, vector] [scalar] [] [0]
  let finiteRoot := math "finiteRoot" [vector, scalar] [scalar]
    [.instruction (.fold "elements" "step" "") [0, 1] [scalar] [] ""] [0]
  let finiteUnit := {snapshot [step, finiteRoot] with domains := [domain]}
  test "ordinary-finite-math-retained" ((check finiteUnit).isOk)
  test "realization-finite-forbidden" (!(check {finiteUnit with definitions :=
    finiteUnit.definitions ++ [.realization ⟨"finiteR", [vector, scalar], [scalar], "finiteRoot"⟩]}).isOk)
  let bounded : Definition := .function ⟨"bounded", .math, .privateDef,
    [vector, .index], [scalar], none, [⟨1, 0, 0⟩], none,
    .block [.instruction (.boundedAt scalarDomain) [0, 1] [scalar] [] ""] (.ret [0])⟩
  test "ordinary-bounded-math-retained" (admits [bounded])
  test "realization-bounded-forbidden" (!admits [bounded,
    .realization ⟨"boundedR", [vector, .index], [scalar], "bounded"⟩])
  let unusedPremise : Definition := .function ⟨"premise", .math, .privateDef,
    [vector, .index], [vector], none, [⟨1, 0, 0⟩], none, .block [] (.ret [0])⟩
  test "realization-unused-premise" (!admits [unusedPremise,
    .realization ⟨"premiseR", [vector, .index], [vector], "premise"⟩])
  -- The whole-unit limit includes the preparation and the protocol owner edges.
  for depth in [61, 62] do
    let definitions := (List.range (depth + 1)).map fun i =>
      math ("h" ++ toString i) [scalar] [scalar]
        (if i == depth then [] else [invokeInstruction ("h" ++ toString (i + 1)) [0] [scalar]]) [0]
    for mapped in [true, false] do
      let ports := if mapped then [vector] else [scalar]
      let preparation := if mapped then
        Definition.map ⟨"prepared", ports, ports, "h0", [true]⟩ else
        Definition.realization ⟨"prepared", ports, ports, "h0"⟩
      let unit := {snapshot (definitions ++ [preparation,
        localApply "wrapper" "prepared" ports ports, localCall "wrapper" ports ports]) with
          entry := "other"}
      test "complete-preparation-depth-edges" (match check unit with
        | .ok _ => depth == 61
        | .error error => depth == 62 && error == "structured-reference-depth")
      test "preparation-availability-depth-edges" (match availabilityPhase unit with
        | .ok _ => depth == 61
        | .error error => depth == 62 && error == "structured-availability-depth-limit")
  let nestedRoot := math "nested" [vector, .index] [vector]
    [invokeInstruction "premiseLeaf" [0, 1] []] [0]
  let premiseLeaf : Definition := .function ⟨"premiseLeaf", .math, .privateDef,
    [vector, .index], [], none, [⟨1, 0, 0⟩], none, .block [] (.ret [])⟩
  let nestedRealization : RealizationDeclaration :=
    ⟨"nestedR", [vector, .index], [vector], "nested"⟩
  let noPremiseLeaf := math "premiseLeaf" [vector, .index] []
  test "nested-zero-call-without-premise" (admits [noPremiseLeaf, nestedRoot,
    .realization nestedRealization])
  test "nested-unused-precondition" (!admits [premiseLeaf, nestedRoot,
    .realization nestedRealization])
  -- Isolate the source premise walk from the ordinary call-premise checker.
  test "nested-precondition-walk" (!(checkPreparationClosure
    (snapshot [premiseLeaf, nestedRoot]) .realization nestedRealization.helperSpec).isOk)
  test "map-derived-budget" (!(snapshot [identity, .map mapDeclaration]).instructionsWithin 0 &&
    (snapshot [identity, .map mapDeclaration]).instructionsWithin 1)
  test "realization-derived-budget" (!(snapshot [identity, .realization realization]).instructionsWithin 0 &&
    (snapshot [identity, .realization realization]).instructionsWithin 1)
  for size in [126, 127] do
    test "shared-definition-limit" ((admits (identity :: (List.range size).map (fun i =>
      .map {mapDeclaration with name := "map" ++ toString i}))) == (size == 126))
  let errors ← failures.get
  if errors.isEmpty then IO.println s!"structured maps: {← count.get} checks passed"
  else throw (IO.userError ("structured maps failed: " ++ String.intercalate ", " errors.reverse))

#eval run
end Tests.StructuredMaps
