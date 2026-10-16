import Zkc.Source.Structured.ClosedProfile
import Zkc.Source.Structured.OpenMeaning
import Mathlib.Algebra.Ring.Int.Defs
import ZkcExamples.Structured.RepeatData
import ZkcExamples.Structured.RepeatNestedData
import ZkcExamples.Structured.RepeatServiceData
import ZkcExamples.Structured.RepeatServiceWrapperData
import ZkcExamples.Structured.SumcheckReduceData
import ZkcExamples.Structured.SumcheckSourceData

open Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredRepeatAdmission

private def protocol (name : String) (inputs outputs : List Ty)
    (inputScopes outputScopes : List (List String)) (body : Block)
    (roles : List String := ["P", "V", "W"]) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs, outputs,
    some ⟨roles, inputScopes, outputScopes⟩, [], none, body⟩

private def unit (definitions : List Definition) : Snapshot :=
  (let contractDefinitions : List Definition := definitions
   ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000",
    "main", [], [], [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none)⟩)

private def repeatInstruction (maximum : Nat := 2) (roles : List String := ["P"])
    (stateScopes : List (List String) := [["P"]])
    (body : Block := .block [] (.yield [1]))
    (inputs : List Ty := [.index, .boolean]) (outputs : List Ty := [.boolean])
    (operands : List Nat := [0, 1]) (carried : Nat := 1)
    (site : String := "loop") : Instruction :=
  .instruction (.protocolRepeat carried maximum roles stateScopes) operands outputs
    [.region inputs outputs body] site

private def root (instruction : Instruction := repeatInstruction)
    (types : List Ty := [.index, .boolean])
    (scopes : List (List String) := [["P"], ["P"]])
    (outputs : List Ty := [.boolean]) (outputScopes : List (List String) := [["P"]])
    (terminal : Terminator := .ret [0]) : Definition :=
  protocol "main" types outputs scopes outputScopes (.block [instruction] terminal)

private def accepted (snapshot : Snapshot) := (check snapshot).isOk
private def refuses (snapshot : Snapshot) (code : String) :=
  match check snapshot with | .error actual => actual == code | .ok _ => false

private def changeRegions (instruction : Instruction) (regions : List WireRegion) : Instruction :=
  let .instruction descriptor operands results _ site := instruction
  .instruction descriptor operands results regions site

private def wire (text : String) : Except String Descriptor :=
  (Format.parse text).bind Format.descriptor

private def wireRefuses (text code : String) :=
  match wire text with | .error actual => actual == code | .ok _ => false

private def service := Ty.service scalarServiceContract
private def scalar := Ty.field scalarDomain

private def serviceChild := protocol "child" [service] [] [["P"]] []
  (.block [.instruction (.draw "P" scalarDomain) [0] [scalar] [] "draw"] (.ret []))

private def serviceRepeat (owner : String := "P") (maximum : Nat := 2) : Definition :=
  root (repeatInstruction maximum ["P"] []
    (.block [.instruction (.protocolApply "child" ["P", "V", "W"]) [1] [] [] "call"] (.yield []))
    [.index, service] [] [0, 1] 0)
    [.index, service] [["P"], [owner]] [] [] (.ret [])

private def oneRoleServiceChild := protocol "child" [service] [] [["A"]] []
  (.block [.instruction (.draw "A" scalarDomain) [0] [scalar] [] "draw"] (.ret [])) ["A"]

private def serviceChain (owner : String := "P") : Definition :=
  let call := Instruction.instruction (.protocolApply "child" ["P"]) [1] [] [] "call"
  let inner := repeatInstruction 2 ["P"] [] (.block [call] (.yield []))
    [.index, service] [] [0, 1] 0 "inner"
  root (repeatInstruction 2 ["P"] [] (.block [inner] (.yield []))
      [.index, service] [] [0, 1] 0)
    [.index, service] [["P"], [owner]] [] [] (.ret [])

private def reorderedServices : Snapshot :=
  let call := Instruction.instruction (.protocolApply "child" ["P"]) [1] [] [] "call"
  let inner := repeatInstruction 0 ["P"] [] (.block [call] (.yield []))
    [.index, service, service] [] [0, 1, 2] 0 "inner"
  let outer := repeatInstruction 0 ["P"] [] (.block [inner] (.yield []))
    [.index, service, service] [] [0, 2, 1] 0 "outer"
  unit [root outer [.index, service, service] [["P"], ["P"], ["P"]] [] [] (.ret []),
    oneRoleServiceChild]

private def statement (maximum : Nat) (noInputs : Bool) : Snapshot :=
  let types := if noInputs then [] else [.boolean]
  let statement := Instruction.instruction (.statement "relation" (if noInputs then [] else ["P"]) 0 none)
    (if noInputs then [] else [2]) [] [] ""
  { unit [root (repeatInstruction maximum ["P"] [["P"]]
      (.block [statement] (.yield [1])) [.index, .boolean, .boolean] [.boolean] [0, 1, 1])] with
    relations := [⟨"relation", .publicDef, "opaque", "key", "revision", types, [.boolean],
      if noInputs then [] else ["statement"], none⟩] }

private def emptyRoot := protocol "main" [] [] [] [] (.block [] (.ret [])) ["P"]

private def nestedFunction (name : String) (count : Nat) (callee : Option String := none) : Definition :=
  let leaf := match callee with
    | none => Block.block [] (.yield [])
    | some callee => .block [.instruction (.protocolApply callee ["P"]) [0] [] [] "call"] (.yield [])
  let body := (List.range count).foldl (fun body i =>
    Block.block [repeatInstruction 0 ["P"] [] body [.index] [] [0] 0 ("loop" ++ toString i)] (.yield [])) leaf
  let .block instructions _ := body
  protocol name [.index] [] [["P"]] [] (.block instructions (.ret [])) ["P"]

private def partialMathSubset : Snapshot :=
  let vector := Ty.vector scalarDomain
  let helper : Definition := .function ⟨"step", .math, .privateDef, [scalar, scalar, vector],
    [scalar], none, [], none, .block [] (.ret [0])⟩
  let callback := Block.block [.instruction (.fold "elements" "step" "") [2, 1] [scalar] [] ""] (.yield [0])
  { unit [root (repeatInstruction (body := callback) (inputs := [.index, scalar, vector])
      (outputs := [scalar]) (operands := [0, 1, 2])) [.index, scalar, vector]
      [["P"], ["P"], ["P"]] [scalar], helper] with
    domains := [⟨"elements", [vector], .elements 0⟩] }

private def metadata (definitions : List Definition) := checkEffectiveProtocolSites (unit definitions)

private def zeroBodyOverBudget : Snapshot :=
  let name := fun i : Nat => "child" ++ toString i
  let call := fun child site => Instruction.instruction (.protocolApply child ["P"]) [0] [] [] site
  let leaf := protocol (name 18) [.index] [] [["P"]] [] (.block [] (.ret [])) ["P"]
  let declarations := (List.range 18).map fun i =>
    protocol (name i) [.index] [] [["P"]] []
      (.block [call (name (i + 1)) "a", call (name (i + 1)) "b"] (.ret [])) ["P"]
  unit (root (repeatInstruction 0 ["P"] [] (.block [call (name 0) "call"] (.yield []))
      [.index] [] [0] 0) [.index] [["P"]] [] [] (.ret []) :: leaf :: declarations)

-- These are kernel-checked ABI and service-origin equations, independent of execution.
example : ProtocolOp.arguments (.repeat ⟨[.boolean], [service], [0], [[0]], 0⟩ "r") =
    [.index, .boolean, service] := rfl
example : ProtocolOp.regions (.repeat ⟨[], [], [0], [], 1048576⟩ "r") =
    [([.index], [])] := rfl
example : repeatOrigins ⟨[.boolean], [.index, service], [0], [[0]], 2⟩
    [3, 1, 3, 2] [some 0, some 1, some 2, some 3] = [none, none, none, some 2] := rfl
example : repeatFacts ⟨[.index], [.index, .vector scalarDomain], [0], [[0]], 2⟩
    [0, 1, 2, 3] [0, 1, 2, 3] [(0, 3), (1, 3), (2, 3)] = [(2, 3)] := by decide +kernel
example : repeatFacts ⟨[.index], [.index, .vector scalarDomain], [0], [[0]], 2⟩
    [0, 1, 3, 2] [40, 50, 70, 60] [(40, 70), (50, 70), (60, 70)] = [(2, 3)] := by decide +kernel

example : accepted (unit [root]) = true := by decide +kernel
example : refuses (statement 0 true) "structured-statement-placement" = true := by decide +kernel
example : (Availability.operation [] ["P"] (.repeat ⟨[], [], [0], [], 0⟩ "loop")
    [[0]]).run {} = .error "structured-protocol-region" := rfl

private def serviceSignature : ProtocolSignature :=
  ⟨"child", ["A"], [service], [], [[0]], []⟩

private def capturedServices : RepeatSpec := ⟨[], [service, service], [0], [], 0⟩

private def reorderedRaw : RawRegion Ty ProtocolOp :=
  .letOp (.mark "outer") [] [] .nil
    (.letOp (.repeat capturedServices "outer") [0, 2, 1] []
      (.cons [.index, service, service] []
        (.letOp (.mark "inner") [] [] .nil
          (.letOp (.repeat capturedServices "inner") [0, 1, 2] []
            (.cons [.index, service, service] []
              (.letOp (.mark "call") [] [] .nil
                (.letOp (.protocolApply serviceSignature [0] "call") [1] [] .nil (.ret []))) .nil)
            (.ret []))) .nil)
      (.ret []))

-- Keep the complete normalized subject explicit, so consumers do not unfold
-- every admission phase again when inspecting one raw operation.
private def reorderedBody : Region protocolDialect [.index, service, service] [] :=
  .letOp (.mark "outer") .nil .nil <|
  .letOp (.repeat capturedServices "outer")
    (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
    (.cons
      (.letOp (.mark "inner") .nil .nil <|
      .letOp (.repeat capturedServices "inner")
        (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
        (.cons
          (.letOp (.mark "call") .nil .nil <|
          .letOp (.protocolApply serviceSignature [0] "call")
            (.cons (.there .here) .nil) .nil (.ret .nil)) .nil)
        (.ret .nil)) .nil)
    (.ret .nil)

private def serviceBody : Region protocolDialect [service] [] :=
  .letOp (.mark "draw") .nil .nil <|
  .letOp (.draw 0 scalarDomain "draw") (.cons .here .nil) .nil (.ret .nil)

private def reorderedSignature : ProtocolSignature :=
  ⟨"main", ["P", "V", "W"], [.index, service, service], [], [[0], [0], [0]], []⟩

private def reorderedDefinition : CheckedProtocol :=
  ⟨reorderedSignature, reorderedBody.erase, reorderedBody, reorderedBody.elaborate_erase⟩

private def serviceDefinition : CheckedProtocol :=
  ⟨serviceSignature, serviceBody.erase, serviceBody, serviceBody.elaborate_erase⟩

private def reorderedPayload : UnitPayload where
  definitions := []
  protocols := [serviceDefinition, reorderedDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

section
set_option smartUnfolding false

private theorem reordered_headers : checkUnitHeaders reorderedServices =
    .ok ([], [reorderedSignature, serviceSignature], []) := rfl

private theorem reordered_helpers : checkUnitHelpers reorderedServices [] [] = .ok [] := rfl

private theorem reordered_protocols :
    checkUnitProtocols reorderedServices [] [] [reorderedSignature, serviceSignature] [] =
      .ok reorderedPayload.protocols := rfl

private theorem reordered_metadata : checkApplicationMetadata reorderedServices = .ok () :=
  checkApplicationMetadata_of_checks (by decide +kernel) (by rfl)

private theorem reordered_linked :
    linkUnitPayload reorderedServices [] reorderedPayload.protocols = .ok reorderedPayload := rfl

private theorem reordered_admitted :
    check reorderedServices = .ok ⟨reorderedServices, reorderedPayload⟩ :=
  check_parts _ _ (check_payload_of_phases reordered_headers reordered_helpers
    reordered_protocols reordered_metadata reordered_linked)

end

private def reorderedImported : Imported reorderedServices :=
  ⟨⟨reorderedServices, reorderedPayload⟩, reordered_admitted⟩

private theorem reordered_entry_raw :
    reorderedImported.program.payload.entry.raw = reorderedRaw := rfl

private theorem reordered_application_occurs :
    .protocolApply serviceSignature [0] "call" ∈ reorderedImported.program.payload.entry.raw.operations := by
  rw [reordered_entry_raw]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

private theorem reordered_entry_member :
    reorderedImported.program.payload.entry ∈ reorderedImported.program.payload.protocols :=
  List.get_mem _ _

/-- The imported role/callee consequences traverse both callbacks. -/
theorem reordered_application_roles :
    [0].length = serviceSignature.roles.length ∧
      (∀ role ∈ [0], role < reorderedImported.program.payload.entry.roles.length) ∧ [0].Nodup :=
  reorderedImported.protocolApplication_roles reordered_entry_member reordered_application_occurs

theorem reordered_application_callee :
    ∃ name function instructions terminal,
      lookupDefinition reorderedServices name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok serviceSignature ∧
      function.body = .block instructions terminal ∧
      instructions.any (fun (.instruction descriptor _ _ _ _) =>
        match descriptor with | .statement .. => true | _ => false) = false :=
  reorderedImported.protocolApplication_callee reordered_entry_member reordered_application_occurs

theorem reordered_application_statementFree :
    ∃ name function,
      lookupDefinition reorderedServices name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok serviceSignature ∧
      function.body.storedInstructions.any Instruction.isStatement = false :=
  reorderedImported.protocolApplication_callee_statementFree
    reordered_entry_member reordered_application_occurs

-- Operand one names original input two, so a single nonnegative root SSA offset
-- cannot describe this lexical origin. It survives the second capture unchanged.
example : repeatOrigins ⟨[], [service, service], [0], [], 0⟩ [0, 1, 2]
    (repeatOrigins ⟨[], [service, service], [0], [], 0⟩ [0, 2, 1] [some 0, some 1, some 2]) =
      [none, some 2, some 1] := rfl

private def outsideSource : Snapshot := unit [protocol "main" [.index] [] [["P", "V"]] []
  (.block [repeatInstruction 0 ["P"] []
    (.block [.instruction (.booleanConstant false) [] [.boolean] [] "",
      .instruction (.guard "P") [0] [] [] "guard"] (.yield []))
    [.index] [] [0] 0] (.ret [])) ["P", "V"]]

private def outsideSignature : ProtocolSignature :=
  ⟨"main", ["P", "V"], [.index], [], [[0, 1]], []⟩

private def outsideBody : Region protocolDialect [.index] [] :=
  .letOp (.mark "loop") .nil .nil <|
  .letOp (.repeat ⟨[], [], [0], [], 0⟩ "loop") (.cons .here .nil)
    (.cons
      (.letOp (.mark "") .nil .nil <|
      .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
      .letOp (.mark "guard") .nil .nil <|
      .letOp (.guard 0 "guard") (.cons .here .nil) .nil (.ret .nil)) .nil)
    (.ret .nil)

private def outsideDefinition : CheckedProtocol :=
  ⟨outsideSignature, outsideBody.erase, outsideBody, outsideBody.elaborate_erase⟩

private def outsidePayload : UnitPayload where
  definitions := []
  protocols := [outsideDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

private def outsideProgram : Program := ⟨outsideSource, outsidePayload⟩

set_option smartUnfolding false in
theorem outside_admission : check outsideSource = .ok outsideProgram :=
  check_parts _ _ (check_payload_of_phases (domains := []) (headers := [outsideSignature])
    (summaries := []) (helpers := []) (protocols := [outsideDefinition])
    (by rfl) (by rfl) (by rfl)
    (checkApplicationMetadata_of_checks (by decide +kernel) (by rfl)) (by rfl))

/-- The admitted root exposes count to both roles, but the repeat includes only
P. Every present outsider count, including excessive logical naturals, retains
the header and reaches neither callback marks nor its rejecting guard. -/
theorem outside_present_count (count : Nat) :
    outsideProgram.observed Int Int 1 (.cons (some count) .nil) =
      .call (.mark "loop") (fun _ => .done .nil) := rfl

example : outsideProgram.observed Int Int 1 (.cons (some (2^128)) .nil) =
    .call (.mark "loop") (fun _ => .done .nil) := outside_present_count _

/-- Static controls check complete units, including zero-maximum and dormant bodies.
Generated full sources are imported verbatim and never sliced by these tests. -/
def run : IO Unit := do
  let checks : List (String × Bool) := [
    ("complete original repeat", accepted ZkcExamples.Structured.RepeatData.snapshot),
    ("complete original nested repeat", accepted ZkcExamples.Structured.RepeatNestedData.snapshot),
    ("complete original service repeat", accepted ZkcExamples.Structured.RepeatServiceData.snapshot),
    ("complete original service wrapper", accepted ZkcExamples.Structured.RepeatServiceWrapperData.snapshot),
    ("entire original Reduction", accepted ZkcExamples.Structured.SumcheckReduceData.snapshot),
    ("entire original Sumcheck", accepted ZkcExamples.Structured.SumcheckSourceData.snapshot),
    ("ordinary retained repeat", accepted (unit [root])),
    ("maximum zero", accepted (unit [root (repeatInstruction 0)])),
    ("maximum endpoint", accepted (unit [root (repeatInstruction 1048576)])),
    ("maximum beyond endpoint", refuses (unit [root (repeatInstruction 1048577)]) "structured-number-limit"),
    ("carried exceeds bound", refuses (unit [root (repeatInstruction (carried := 513))]) "structured-number-limit"),
    ("carried equals operand count", refuses (unit [root (repeatInstruction (carried := 2))]) "structured-protocol-signature"),
    ("wrong count type", refuses (unit [root (repeatInstruction (inputs := [.boolean, .boolean]))
      [.boolean, .boolean]]) "structured-protocol-signature"),
    ("wrong result type", refuses (unit [root (repeatInstruction (outputs := [.index]))]) "structured-protocol-signature"),
    ("wrong result count", refuses (unit [root (repeatInstruction (outputs := []))]) "structured-protocol-signature"),
    ("zero callbacks", refuses (unit [root (changeRegions repeatInstruction [])]) "structured-protocol-region"),
    ("two callbacks", refuses (unit [root (changeRegions repeatInstruction
      (List.replicate 2 (.region [.index, .boolean] [.boolean] (.block [] (.yield [1])))))])
      "structured-protocol-region"),
    ("wrong callback input", refuses (unit [root (repeatInstruction (inputs := [.boolean, .boolean]))])
      "structured-protocol-signature"),
    ("wrong callback output", refuses (unit [root (changeRegions repeatInstruction
      [.region [.index, .boolean] [] (.block [] (.yield []))])]) "structured-protocol-signature"),
    ("return in callback", refuses (unit [root (repeatInstruction (body := .block [] (.ret [1])))])
      "structured-protocol-terminator"),
    ("condition in callback", refuses (unit [root (repeatInstruction (body := .block [] (.condition [1])))])
      "structured-protocol-terminator"),
    ("stop in callback", refuses (unit [root (repeatInstruction (body := .block [] (.stop .reject "stop")))])
      "structured-protocol-terminator"),
    ("yield at root", refuses (unit [root (terminal := .yield [0])]) "structured-protocol-terminator"),
    ("wrong yield arity", refuses (unit [root (repeatInstruction (body := .block [] (.yield [])))]) "structured-formation"),
    ("wrong yield type", refuses (unit [root (repeatInstruction (body := .block [] (.yield [0])))]) "structured-formation"),
    ("isolated outer reference", refuses (unit [root (repeatInstruction (body := .block [] (.yield [2])))]) "structured-formation"),
    ("explicit captured replacement", accepted (unit [root (repeatInstruction (body := .block [] (.yield [2]))
      (inputs := [.index, .boolean, .boolean]) (operands := [0, 1, 1]))])),
    ("empty roster", refuses (unit [root (repeatInstruction (roles := []))]) "structured-scope"),
    ("duplicate roster", refuses (unit [root (repeatInstruction (roles := ["P", "P"]))]) "structured-scope"),
    ("foreign roster", refuses (unit [root (repeatInstruction (roles := ["unknown"]))]) "structured-role"),
    ("empty state scope", refuses (unit [root (repeatInstruction (stateScopes := [[]]))]) "structured-scope"),
    ("duplicate state scope", refuses (unit [root (repeatInstruction (stateScopes := [["P", "P"]]))]) "structured-scope"),
    ("scope outside roster", refuses (unit [root (repeatInstruction (stateScopes := [["V"]]))]) "structured-scope"),
    ("state scope count", refuses (unit [root (repeatInstruction (stateScopes := []))]) "structured-scope-count"),
    ("count footprint max zero", refuses (unit [root (repeatInstruction 0 ["P", "V"])]) "structured-repeat-count-scope"),
    ("initial state footprint", refuses (unit [root (scopes := [["P"], ["V"]])]) "structured-repeat-state-scope"),
    ("yield footprint", refuses (unit [root (repeatInstruction (roles := ["P", "V"])
      (body := .block [] (.yield [2])) (inputs := [.index, .boolean, .boolean]) (operands := [0, 1, 2]))
      [.index, .boolean, .boolean] [["P", "V"], ["P"], ["V"]]]) "structured-repeat-yield-scope"),
    ("unused yield footprint max zero", refuses (unit [root (repeatInstruction 0 ["P", "V"]
      (body := .block [] (.yield [2])) (inputs := [.index, .boolean, .boolean]) (operands := [0, 1, 2]))
      [.index, .boolean, .boolean] [["P", "V"], ["P"], ["V"]] [] [] (.ret [])])
      "structured-repeat-yield-scope"),
    ("disjoint unused capture", refuses (unit [root (repeatInstruction (inputs := [.index, .boolean, .boolean])
      (operands := [0, 1, 2])) [.index, .boolean, .boolean] [["P"], ["P"], ["V"]]])
      "structured-repeat-capture-scope"),
    ("nullary calculation cannot authorize foreign action", refuses (unit [root (repeatInstruction
      (body := .block [.instruction (.booleanConstant true) [] [.boolean] [] "",
        .instruction (.guard "W") [0] [] [] "guard"] (.yield [2])))]) "structured-repeat-role"),
    ("nested repeat cannot enlarge roster", refuses (unit [root (repeatInstruction (body := .block
      [repeatInstruction 0 ["P", "V"] [["P"]] (site := "inner")] (.yield [0])))]) "structured-repeat-role"),
    ("nested statement with data max zero", refuses (statement 0 false) "structured-statement-placement"),
    ("nested statement without operands max zero", refuses (statement 0 true) "structured-statement-placement"),
    ("nested statement with data positive", refuses (statement 2 false) "structured-statement-placement"),
    ("nested statement without operands positive", refuses (statement 2 true) "structured-statement-placement"),
    ("nested service capture and application", accepted (unit [serviceChain, oneRoleServiceChild])),
    ("reordered nested service captures", accepted reorderedServices),
    ("nested foreign service capture", refuses (unit [serviceChain "V", oneRoleServiceChild])
      "structured-service-owner"),
    ("unused captured service formal still checks owner", refuses (unit [serviceChain "V",
      protocol "child" [service] [] [["A"]] [] (.block [] (.ret [])) ["A"]])
      "structured-service-owner"),
    ("service state max zero", refuses (unit [root (repeatInstruction 0 (inputs := [.index, service])
      (outputs := [service])) [.index, service]]) "structured-protocol-signature"),
    ("service yield as data", refuses (unit [root (repeatInstruction (body := .block [] (.yield [2]))
      (inputs := [.index, .boolean, service]) (operands := [0, 1, 2]))
      [.index, .boolean, service] [["P"], ["P"], ["P"]]]) "structured-formation"),
    ("header and child collision max zero", refuses (unit [root (repeatInstruction 0
      (body := .block [.instruction (.guard "P") [1] [] [] "loop"] (.yield [1])))])
      "structured-duplicate-site"),
    ("closed retained repeat diagnostic", match checkClosed (unit [protocol "main" [.index, .boolean] [.boolean]
      [["P"], ["P"]] [["P"]] (.block [repeatInstruction] (.ret [0])) ["P"]]) with
      | .error code => code == "structured-protocol-region" | .ok _ => false),
    ("dormant supported repeat with closed empty root", (checkClosed (unit [emptyRoot,
      protocol "dormant" [.index, .boolean] [.boolean] [["P"], ["P"]] [["P"]]
        (.block [repeatInstruction] (.ret [0]))])).isOk),
    ("zero state and zero captures", accepted (unit [root (repeatInstruction 0 ["P"] []
      (.block [] (.yield [])) [.index] [] [0] 0) [.index] [["P"]] [] [] (.ret [])])),
    ("zero state with unused explicit capture", accepted (unit [root (repeatInstruction 2 ["P"] []
      (.block [] (.yield [])) [.index, .boolean] [] [0, 1] 0)
      [.index, .boolean] [["P"], ["P"]] [] [] (.ret [])])),
    ("captured original count distinct from induction", accepted (unit [root (repeatInstruction
      (body := .block [.instruction .indexEqual [0, 2] [.boolean] [] ""] (.yield [0]))
      (inputs := [.index, .boolean, .index]) (operands := [0, 1, 0]))])),
    ("unknown application in zero callback", refuses (unit [root (repeatInstruction 0
      (body := .block [.instruction (.protocolApply "missing" ["P"]) [] [] [] "call"] (.yield [1])))])
      "structured-unknown-helper"),
    ("stopping prefix does not hide unresolved zero callback", refuses (unit [
      protocol "main" [.index, .boolean] [.boolean] [["P"], ["P"]] [["P"]]
        (.block [.instruction (.booleanConstant false) [] [.boolean] [] "",
          .instruction (.guard "P") [0] [] [] "stop",
          repeatInstruction 0 (operands := [1, 2]) (body := .block
            [.instruction (.protocolApply "missing" ["P"]) [] [] [] "call"] (.yield [1]))]
          (.ret [0]))]) "structured-unknown-helper"),
    ("zero callback does not hide over-budget expansion", refuses zeroBodyOverBudget
      "structured-application-limit"),
    ("self application in callback still cyclic", refuses (unit [root (repeatInstruction 0
      (roles := ["P", "V", "W"]) (body := .block [.instruction
        (.protocolApply "main" ["P", "V", "W"]) [0, 1] [.boolean] [] "call"] (.yield [0])))
      (scopes := [["P", "V", "W"], ["P"]])]) "structured-protocol-cycle"),
    ("dormant zero callback checked", refuses (unit [emptyRoot,
      protocol "dormant" [.index, .boolean] [.boolean] [["P"], ["P"]] [["P"]]
        (.block [repeatInstruction 0 (body := .block [] (.ret [1]))] (.ret [0]))])
      "structured-protocol-terminator"),
    ("nested apply cannot enlarge roster", refuses (unit [serviceRepeat, serviceChild])
      "structured-repeat-role"),
    ("generated child collides with repeat header", refuses (unit [root (repeatInstruction 0
      (body := .block [.instruction (.protocolApply "guarded" ["P"]) [1] [] [] "a"] (.yield [1]))
      (site := "apply_1_a_q")),
      protocol "guarded" [.boolean] [] [["A"]] []
        (.block [.instruction (.guard "A") [0] [] [] "q"] (.ret [])) ["A"]])
      "structured-effective-site-collision"),
    ("singleton repeat preserves containing multi-role partial Math refusal",
      refuses partialMathSubset "structured-availability-partial-math"),
    ("exact descriptor", (wire "[\"protocol_repeat\",1,2,[\"P\"],[[\"P\"]]]").isOk),
    ("descriptor missing field", wireRefuses "[\"protocol_repeat\",1,2,[\"P\"]]" "structured-operation-unsupported"),
    ("descriptor extra field", wireRefuses "[\"protocol_repeat\",1,2,[\"P\"],[[\"P\"]],0]" "structured-operation-unsupported"),
    ("negative carried", wireRefuses "[\"protocol_repeat\",-1,2,[\"P\"],[]]" "expected-natural"),
    ("negative maximum", wireRefuses "[\"protocol_repeat\",0,-1,[\"P\"],[]]" "expected-natural"),
    ("wire maximum endpoint", (wire "[\"protocol_repeat\",0,1048576,[\"P\"],[]]").isOk),
    ("wire maximum beyond endpoint", wireRefuses "[\"protocol_repeat\",0,1048577,[\"P\"],[]]" "structured-number-limit"),
    ("wire carried endpoint", (wire "[\"protocol_repeat\",512,0,[\"P\"],[]]").isOk),
    ("wire carried beyond endpoint", wireRefuses "[\"protocol_repeat\",513,0,[\"P\"],[]]" "structured-number-limit"),
    ("wire number string", wireRefuses "[\"protocol_repeat\",\"1\",0,[\"P\"],[]]" "structured-natural"),
    ("repeat selectors exclude state scopes", (ApplicationMetadata.instructionCost
      (repeatInstruction 0 ["P", "V"] [["P", "V"]])).selectors == 2),
    ("static accounting independent of maximum", match checkNativeApplicationBudgets (unit [root (repeatInstruction 0)]),
        checkNativeApplicationBudgets (unit [root (repeatInstruction 1048576)]) with
      | .ok left, .ok right => left == right | _, _ => false),
    ("wire array depth 64 is an independent capacity", (Format.parse
      (String.ofList (List.replicate 64 '[') ++ String.ofList (List.replicate 64 ']'))).isOk),
    ("wire array depth 65 refuses before decoding", match Format.parse
      (String.ofList (List.replicate 65 '[') ++ String.ofList (List.replicate 65 ']')) with
      | .error code => code == "depth-limit" | .ok _ => false),
    ("expanded nesting 64 across apply", (metadata [nestedFunction "main" 32 (some "child"),
      nestedFunction "child" 32]).isOk),
    ("expanded nesting 65 across apply", match metadata [nestedFunction "main" 32 (some "child"),
      nestedFunction "child" 33] with
      | .error code => code == "structured-repeat-depth" | .ok _ => false)]
  let mut failed := 0
  for (name, passed) in checks do
    if !passed then
      IO.eprintln s!"FAIL: {name}"
      failed := failed + 1
  if failed != 0 then throw (IO.userError s!"{failed} repeat admission controls failed")
  IO.println s!"{checks.length} structured repeat admission controls passed"

#eval run

end Tests.StructuredRepeatAdmission
