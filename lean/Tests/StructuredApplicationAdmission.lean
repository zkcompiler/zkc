import Zkc.Source.Structured.Import
import Zkc.Source.Structured.ModelAdmission
import ZkcExamples.Structured.ApplicationData
import ZkcExamples.Structured.ServiceOrderData
import ZkcExamples.Structured.ServiceOrderViews

open Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredApplicationAdmission

private def protocol (name : String) (roles : List String) (inputs outputs : List Ty)
    (inputScopes outputScopes : List (List String)) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs, outputs,
    some ⟨roles, inputScopes, outputScopes⟩, [], none, body⟩

private def unit (definitions : List Definition) (entry : String := "main") : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000",
    entry, [], [], [], definitions⟩

private def child := protocol "child" ["A", "B"] [.boolean, .boolean] [.boolean]
  [["A"], ["B"]] [["A"]] (.block [] (.ret [0]))

private def caller (roles : List String := ["P", "V"])
    (operands : List Nat := [0, 1]) (site : String := "call") :=
  protocol "main" ["P", "V", "W"] [.boolean, .boolean] [.boolean]
    [["P"], ["V"]] [["P"]]
    (.block [.instruction (.protocolApply "child" roles) operands [.boolean] [] site] (.ret [0]))

private def empty (name : String) (instructions : List Instruction := []) :=
  protocol name ["P"] [] [] [] [] (.block instructions (.ret []))

private def call (name site : String) : Instruction :=
  .instruction (.protocolApply name ["P"]) [] [] [] site

private def accepted (snapshot : Snapshot) := (check snapshot).isOk

private def refusal {α : Type} (result : Except String α) (expected : String) : Bool :=
  match result with | .error code => code == expected | .ok _ => false

private def changedFunction (definition : Definition) (change : Function → Function) : Definition :=
  match definition with | .function function => .function (change function) | other => other

private def service := Ty.service scalarServiceContract
private def scalar := Ty.field scalarDomain
private def serviceChild := protocol "serviceChild" ["A"] [service, service] []
  [["A"], ["A"]] [] (.block [] (.ret []))
private def serviceCaller (operands : List Nat) :=
  protocol "main" ["P", "V"] [service, service] [] [["P"], ["V"]] []
    (.block [.instruction (.protocolApply "serviceChild" ["P"]) operands [] [] "use"] (.ret []))

private def collision (leafSite : String) := unit [
  protocol "main" ["P"] [.boolean] [] [["P"]] []
    (.block [.instruction (.guard "P") [0] [] [] leafSite,
      .instruction (.protocolApply "guarded" ["P"]) [0] [] [] "a"] (.ret [])),
  protocol "guarded" ["X"] [.boolean] [] [["X"]] []
    (.block [.instruction (.guard "X") [0] [] [] "b"] (.ret []))]

private def chain (length : Nat) : Snapshot :=
  unit ((List.range length).map fun index =>
    empty ("p" ++ toString index)
      (if index + 1 < length then [call ("p" ++ toString (index + 1)) "next"] else [])) "p0"

private def structuredOnly (snapshot : Snapshot) : Bool :=
  ((do
    let (domains, headers, summaries) ← checkUnitHeaders snapshot
    let helpers ← checkUnitHelpers snapshot domains summaries
    checkUnitProtocols snapshot domains summaries headers helpers) :
      Except String (List CheckedProtocol)).isOk

private def nativeWork (padding : Nat) :=
  let pureOp := Instruction.instruction (.booleanConstant true) [] [.boolean] [] ""
  let helper : Definition := .function ⟨"many", .math, .privateDef, [], [], none, [], none,
    .block (List.replicate 998 pureOp) (.ret [])⟩
  unit [empty "main" (List.replicate 99 (.instruction (.call "many") [] [] [] "") ++
    List.replicate padding pureOp), helper]

private def subsetFold (calleeRoles : List String) : Snapshot :=
  let vector := Ty.vector scalarDomain
  let helper : Definition := .function ⟨"step", .math, .privateDef,
    [scalar, scalar, vector], [scalar], none, [], none, .block [] (.ret [0])⟩
  let callee := protocol "foldLeaf" calleeRoles [vector, scalar] [scalar]
    [["A"], ["A"]] [["A"]]
    (.block [.instruction (.fold "elements" "step" "") [0, 1] [scalar] [] ""] (.ret [0]))
  let caller := protocol "main" ["P", "V"] [vector, scalar] [scalar]
    [["P"], ["P"]] [["P"]]
    (.block [.instruction (.protocolApply "foldLeaf" (if calleeRoles.length == 1 then ["P"] else ["P", "V"]))
      [0, 1] [scalar] [] "apply"] (.ret [0]))
  { unit [caller, callee, helper] with domains := [⟨"elements", [vector], .elements 0⟩] }

private def statementUnit (called : Bool) : Snapshot :=
  let root := protocol "main" ["P"] [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.statement "relation" ["P"] 0) [0] [] [] ""] (.ret [0]))
  let dormant := protocol "dormant" ["P"] [.boolean] [] [["P"]] []
    (.block [.instruction (.protocolApply "main" ["P"]) [0] [.boolean] [] "apply"] (.ret []))
  { unit (if called then [root, dormant] else [root]) with
    relations := [⟨"relation", .publicDef, "opaque", "key", "rev",
      [.boolean], [.boolean], ["statement"]⟩] }

private def erasedHeader := unit [
  protocol "main" ["P"] [.boolean] [] [["P"]] []
    (.block [.instruction (.guard "P") [0] [] [] "apply_1_a_b", call "child" "a"] (.ret [])),
  empty "child" [call "leaf" "b"], empty "leaf"]

private def secondCollision := unit [
  protocol "main" ["P"] [.boolean] [] [["P"]] []
    (.block [.instruction (.guard "P") [0] [] [] "apply_1_b_c",
      .instruction (.protocolApply "leaf" ["P"]) [0] [] [] "a",
      .instruction (.protocolApply "leaf" ["P"]) [0] [] [] "b"] (.ret [])),
  protocol "leaf" ["P"] [.boolean] [] [["P"]] []
    (.block [.instruction (.guard "P") [0] [] [] "c"] (.ret []))]

private def helperNamespace := unit [
  protocol "main" ["P"] [.boolean] [] [["P"]] []
    (.block [.instruction (.guard "P") [0] [] [] "shared",
      .instruction (.localCall "helper" "P") [] [] [] "invoke"] (.ret [])),
  .function ⟨"helper", .local, .privateDef, [], [], none, [], some ("helper", []),
    .block [] (.stop .reject "shared")⟩]

private def render (parent : Option String) (leaf : String)
    (bytes : Nat := 0) : Except String String :=
  (ApplicationMetadata.renderSite parent leaf).run' { bytes := bytes }

private def chars (size : Nat) : String := String.ofList (List.replicate size 'a')

private def wireAccepted (text : String) : Bool :=
  ((Format.parse text).bind Format.descriptor).isOk

-- Small kernel controls accompany executable whole-unit and threshold checks.
example : (ProtocolSignature.mk "p" ["P"] [.boolean] [.boolean] [[0]] [[0]]) ≠
    (ProtocolSignature.mk "p" ["P"] [.boolean] [.boolean] [[0]] [[]]) := by decide
example : ProtocolOp.regions (.protocolApply ⟨"p", ["P"], [], [], [], []⟩ [0] "call") = [] := rfl
example : accepted (unit [caller, child]) = true := by decide +kernel
example : accepted (unit [caller ["P", "P"], child]) = false := by decide +kernel

/- These controls use the complete unchanged source and its single named
kernel admission. The call follows a draw, so its service operands have shifted
SSA positions; membership is in the recursive raw inventory, not a signature
inventory or a hand-built imported program. -/
open ZkcExamples.Structured.ServiceOrderBodies ZkcExamples.Structured.ServiceOrderViews

theorem serviceOrder_application_occurs :
    .protocolApply drawSignature [0, 1] "s3" ∈ runDefinition.raw.operations := by
  rw [run_raw]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem serviceOrder_application_roles :
    [0, 1].length = drawSignature.roles.length ∧
      (∀ role ∈ [0, 1], role < runDefinition.roles.length) ∧ [0, 1].Nodup :=
  imported.protocolApplication_roles run_member serviceOrder_application_occurs

theorem serviceOrder_application_origin :
    ∃ function domains headers summaries interface instructions terminal offset name roles operands regions,
      .function function ∈ ZkcExamples.Structured.ServiceOrderData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders ZkcExamples.Structured.ServiceOrderData.snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol ZkcExamples.Structured.ServiceOrderData.snapshot domains summaries function headers =
        .ok runDefinition ∧
      function.interface = some interface ∧ runDefinition.roles = interface.roles ∧
      function.body = .block instructions terminal ∧
      .instruction (.protocolApply name roles) operands drawSignature.outputs regions "s3" ∈ instructions ∧
      validProtocolIdentifier "s3" = true ∧
      resolveProtocolApplication ZkcExamples.Structured.ServiceOrderData.snapshot headers interface name roles =
        .ok (drawSignature, [0, 1]) ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (drawSignature.inputs.zip drawSignature.inputScopes).zip operands → type.isService = true →
        ∃ input, operand = offset + input ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => [0, 1][role]?.getD 0)).length = 1 ∧
          runDefinition.inputScopes[input]? = some (scope.map (fun role => [0, 1][role]?.getD 0))) :=
  imported.protocolApplication run_member serviceOrder_application_occurs

theorem serviceOrder_application_callee :
    ∃ name function instructions terminal,
      lookupDefinition ZkcExamples.Structured.ServiceOrderData.snapshot name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok drawSignature ∧
      function.body = .block instructions terminal ∧
      instructions.any (fun (.instruction descriptor _ _ _ _) =>
        match descriptor with | .statement .. => true | _ => false) = false :=
  imported.protocolApplication_callee run_member serviceOrder_application_occurs

theorem serviceOrder_protocol_permutation :
    ∃ domains headers summaries formed,
      checkUnitHeaders ZkcExamples.Structured.ServiceOrderData.snapshot = .ok (domains, headers, summaries) ∧
      ZkcExamples.Structured.ServiceOrderData.snapshot.protocolFunctions.mapM (fun function =>
        checkProtocol ZkcExamples.Structured.ServiceOrderData.snapshot domains summaries function headers) =
          .ok formed ∧
      [drawDefinition, runDefinition].Perm formed :=
  imported.protocolPermutation

/-- The default header table is only an application-free convenience. -/
theorem application_without_headers_refused :
    checkProtocol (unit [caller, child]) [] []
      ⟨"main", .protocol, .publicDef, [.boolean, .boolean], [.boolean],
        some ⟨["P", "V", "W"], [["P"], ["V"]], [["P"]]⟩, [], none,
        .block [.instruction (.protocolApply "child" ["P", "V"]) [0, 1] [.boolean] [] "call"] (.ret [0])⟩ =
      .error "structured-protocol-header" := rfl

/-- Independently authored source controls; no hand-built tree is labeled a source fixture. -/
def run : IO Unit := do
  let checks : List (String × Bool) := [
    ("complete original application", accepted ZkcExamples.Structured.ApplicationData.snapshot),
    ("complete original service order", accepted ZkcExamples.Structured.ServiceOrderData.snapshot),
    ("forward declaration and proper subset", accepted (unit [caller, child])),
    ("unused actual input scope checked", !accepted (unit [caller ["P", "W"], child])),
    ("duplicate role", !accepted (unit [caller ["P", "P"], child])),
    ("foreign role", !accepted (unit [caller ["P", "foreign"], child])),
    ("missing role", !accepted (unit [caller ["P"], child])),
    ("extra role", !accepted (unit [caller ["P", "V", "W"], child])),
    ("ordered argument scopes", !accepted (unit [caller ["P", "V"] [1, 0], child])),
    ("missing unused argument", !accepted (unit [caller ["P", "V"] [0], child])),
    ("nonidentifier site", !accepted (unit [caller ["P", "V"] [0, 1] "bad-site", child])),
    ("nonascii site", !accepted (unit [caller ["P", "V"] [0, 1] "가", child])),
    ("empty real site", !accepted (unit [caller ["P", "V"] [0, 1] "", child])),
    ("source site 513 bytes", !accepted (unit [caller ["P", "V"] [0, 1]
      (String.ofList (List.replicate 513 'a')), child])),
    ("dormant private protocol", !accepted (unit [empty "main",
      changedFunction (empty "dormant") fun f => { f with visibility := .privateDef }])),
    ("malformed dormant body", !accepted (unit [empty "main",
      changedFunction (empty "dormant") fun f => { f with body := .block [] (.ret [0]) }])),
    ("dormant self cycle", !accepted (unit [empty "main", empty "dormant" [call "dormant" "a"]])),
    ("dormant mutual cycle", !accepted (unit [empty "main", empty "x" [call "y" "a"],
      empty "y" [call "x" "b"]])),
    ("selected root may be called", accepted (unit [empty "main", empty "caller" [call "main" "a"]])),
    ("wrong original Math edge", !accepted (unit [empty "main" [call "math" "a"],
      .function ⟨"math", .math, .privateDef, [], [], none, [], none, .block [] (.ret [])⟩])),
    ("wrong original Local edge", !accepted (unit [empty "main" [call "local" "a"],
      .function ⟨"local", .local, .privateDef, [], [], none, [], some ("local", []), .block [] (.ret [])⟩])),
    ("Math invocation of protocol", !accepted (unit [empty "main"
      [.instruction (.call "child") [] [] [] ""], empty "child"])),
    ("service aliases legal", accepted (unit [serviceCaller [0, 0], serviceChild])),
    ("service owner independent of handle", !accepted (unit [serviceCaller [0, 1], serviceChild])),
    ("effective generated collision", !accepted (collision "apply_1_a_b")),
    ("model retains site identity", refusal (checkFormedPayload (collision "apply_1_a_b"))
      "structured-effective-site-collision"),
    ("generated-looking label harmless", accepted (collision "apply_1_a_c")),
    ("source namespace duplicate", !accepted (unit [empty "main" [call "child" "a", call "child" "a"], empty "child"])),
    ("structured 64 edges accepted", structuredOnly (chain 65)),
    ("structured 65 edges refused", !structuredOnly (chain 66)),
    ("native depth 64", (checkNativeApplicationBudgets (chain 64)).isOk),
    ("native depth 65", !(checkNativeApplicationBudgets (chain 65)).isOk),
    ("whole-unit depth 65", !accepted (chain 65)),
    ("native depth refusal precedes site traversal", refusal (check (chain 65))
      "structured-application-depth"),
    ("model retains site traversal capacity", refusal (checkFormedPayload (chain 65))
      "structured-effective-site-depth"),
    ("native work 100000", (checkNativeApplicationBudgets (nativeWork 999)).isOk),
    ("native work 100001", !(checkNativeApplicationBudgets (nativeWork 1000)).isOk),
    ("metadata visits shared across roots", !(checkEffectiveProtocolSites
      (unit [empty "main" (List.replicate 50000 (.instruction (.booleanConstant true) [] [.boolean] [] "")),
        empty "dormant" (List.replicate 50000 (.instruction (.booleanConstant true) [] [.boolean] [] ""))])).isOk),
    ("current descriptor accepted", wireAccepted "[\"protocol_apply\",\"p\",[\"P\"]]"),
    ("descriptor extra field", !wireAccepted "[\"protocol_apply\",\"p\",[\"P\"],0]"),
    ("descriptor missing field", !wireAccepted "[\"protocol_apply\",\"p\"]"),
    ("descriptor numeric role", !wireAccepted "[\"protocol_apply\",\"p\",[0]]"),
    ("descriptor null role", !wireAccepted "[\"protocol_apply\",\"p\",[null]]"),
    ("descriptor numeric callee", !wireAccepted "[\"protocol_apply\",0,[\"P\"]]"),
    ("one-role partial Math subset callee", accepted (subsetFold ["A"])),
    ("multi-role partial Math remains refused", !accepted (subsetFold ["A", "B"])),
    ("applied selected statement refused", !accepted (statementUnit true)),
    ("unapplied selected statement accepted", accepted (statementUnit false)),
    ("erased header does not collide", accepted erasedHeader),
    ("second shared callee occurrence collides", !accepted secondCollision),
    ("helper namespace independent", accepted helperNamespace),
    ("apply nonempty regions", !accepted (unit [
      protocol "main" ["P", "V"] [.boolean, .boolean] [.boolean]
        [["P"], ["V"]] [["P"]]
        (.block [.instruction (.protocolApply "child" ["P", "V"]) [0, 1] [.boolean]
          [.region [] [] (.block [] (.ret []))] "call"] (.ret [0])), child])),
    ("wrong result ABI", !accepted (unit [
      protocol "main" ["P", "V"] [.boolean, .boolean] [.index]
        [["P"], ["V"]] [["P"]]
        (.block [.instruction (.protocolApply "child" ["P", "V"]) [0, 1] [.index]
          [] "call"] (.ret [0])), child])),
    ("service result rejected", !accepted (unit [protocol "main" ["P"] [service] [service]
      [["P"]] [["P"]] (.block [] (.ret [0]))])),
    ("fabricated service rejected", !accepted (unit [protocol "main" ["P"] [] [] [] []
      (.block [.instruction (.booleanConstant true) [] [service] [] "",
        .instruction (.protocolApply "serviceChild" ["P"]) [0, 0] [] [] "call"] (.ret [])), serviceChild])),
    ("service after SSA result shift", accepted (unit [protocol "main" ["P"] [service] [] [["P"]] []
      (.block [.instruction (.booleanConstant true) [] [.boolean] [] "",
        .instruction (.protocolApply "serviceChild" ["P"]) [1, 1] [] [] "call"] (.ret [])), serviceChild])),
    ("wrong lexical input after shift", !accepted (unit [protocol "main" ["P"] [service] [] [["P"]] []
      (.block [.instruction (.booleanConstant true) [] [.boolean] [] "",
        .instruction (.protocolApply "serviceChild" ["P"]) [0, 1] [] [] "call"] (.ret [])), serviceChild])),
    ("nonidentifier protocol name", !accepted (unit [empty "main", empty "bad-name"])),
    ("private Math symbol grammar independent", accepted (unit [empty "main",
      .function ⟨"private.math-name", .math, .privateDef, [], [], none, [], none, .block [] (.ret [])⟩])),
    ("nonidentifier roster", !accepted (unit [protocol "main" ["P-x"] [] [] [] [] (.block [] (.ret []))])),
    ("nonascii roster", !accepted (unit [protocol "main" ["가"] [] [] [] [] (.block [] (.ret []))])),
    ("generated 513 bytes allowed", (render (some (chars 497)) (chars 5)).isOk),
    ("generated 4096 bytes allowed", (render (some (chars 4000)) (chars 84)).isOk),
    ("generated 4097 bytes refused", !(render (some (chars 4000)) (chars 85)).isOk),
    ("cumulative label exact bound", (render none "a" 16777215).isOk),
    ("cumulative label overflow", !(render none "a" 16777216).isOk),
    ("native slots exact bound", (ApplicationMetadata.addOriginal
      { indices := 999998 } ⟨none, 1, 1, ""⟩).isOk),
    ("native slots overflow", !(ApplicationMetadata.addOriginal
      { indices := 999999 } ⟨none, 1, 1, ""⟩).isOk),
    ("native conservative prefix", !(ApplicationMetadata.addChild {} { sites := 1, longestSite := 4084 }
      0 0 13 true).isOk),
    ("Math child sites excluded", (ApplicationMetadata.addChild {} { sites := 1, longestSite := 4096 }
      0 0 0 false).isOk),
    ("unsupported repeat", !wireAccepted "[\"repeat\"]"),
    ("unsupported completion", !wireAccepted "[\"finish_if\"]"),
    ("unsupported construction", !wireAccepted "[\"construction_start\"]")]
  let mut failures := 0
  for (label, passed) in checks do
    if !passed then
      IO.eprintln s!"FAIL: {label}"
      failures := failures + 1
  if failures != 0 then throw (IO.userError s!"{failures} admission controls failed")
  IO.println s!"{checks.length} structured application admission controls passed"

#eval run

end Tests.StructuredApplicationAdmission
