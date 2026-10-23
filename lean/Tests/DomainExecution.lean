import Zkc.Construction.DomainExecutionLaws
import Mathlib.Data.ZMod.Basic

/-! Small admitted fixtures for constructed producer and validator execution.
The mixed carriers below are operational test data, not extension-field laws. -/
set_option autoImplicit false
set_option smartUnfolding false
namespace Tests.DomainExecution
open Zkc.Source
open Zkc.Construction
open Zkc.Construction.Domain

private def model : Structured.DomainModel where
  Field d := if d = "base" then Int else ZMod 5
  Group _ := Int
  fieldRing d := by split <;> infer_instance
  fieldDecEq d := by split <;> infer_instance
  inverse _ := none
  embed extension _ _ := by split <;> exact 0
  groupAdd _ := inferInstance
  groupDecEq _ := inferInstance
  smul _ _ _ _ := 0

private def context : Context :=
  ⟨"main", ["P", "V"], 0, 1, 0, "random.extension/0", some (.draw "extension"), "suite", []⟩

private def helper (swapped : Bool) : Structured.Definition :=
  .function ⟨"pair", .math, .privateDef, [.boolean, .boolean], [.boolean, .boolean],
    none, [], none, .block [] (.ret (if swapped then [1, 0] else [0, 1]))⟩
private def stoppingHelper : Structured.Definition :=
  .function ⟨"stop", .local, .privateDef, [], [], none, [], some ("stop", []),
    .block [] (.stop .abort "stop")⟩
private def snapshot (swapped : Bool := false) : Structured.Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [helper swapped, stoppingHelper,
    .function ⟨"main", .protocol, .publicDef, [], [], some ⟨["P", "V"], [], []⟩,
      [], none, .block [] (.ret [])⟩]
  contracts := [⟨"main", []⟩]
  catalogue := ⟨[], [], []⟩
private def pairBody (swapped : Bool) : Region Structured.dialect
    [.boolean, .boolean] [.boolean, .boolean] :=
  if swapped then .ret (.cons (.there .here) (.cons .here .nil))
  else .ret (.cons .here (.cons (.there .here) .nil))
private def pairDefinition (swapped : Bool) : Structured.CheckedDefinition :=
  ⟨"pair", .math, [.boolean, .boolean], [.boolean, .boolean],
    (pairBody swapped).erase, pairBody swapped, (pairBody swapped).elaborate_erase⟩
private def stopBody : Region Structured.dialect [] [] :=
  .letOp (.mark "stop") .nil .nil (.stop .abort)
private def stopDefinition : Structured.CheckedDefinition :=
  ⟨"stop", .local, [], [], stopBody.erase, stopBody, stopBody.elaborate_erase⟩
private def mainBody : Region Structured.protocolDialect [] [] := .ret .nil
private def mainDefinition : Structured.CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [], [], [], []⟩, mainBody.erase, mainBody, mainBody.elaborate_erase⟩
private def unit (swapped : Bool) : Structured.UnitPayload where
  definitions := [pairDefinition swapped, stopDefinition]
  protocols := [mainDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by cases swapped <;> decide +kernel
  protocolsLinked := by cases swapped <;> decide +kernel
  available := by cases swapped <;> rfl
  realizationClosed := by cases swapped <;> decide +kernel
  mapClosed := by cases swapped <;> decide +kernel
private def program (swapped : Bool := false) : Structured.Program := ⟨snapshot swapped, unit swapped⟩

set_option smartUnfolding false in
example (swapped : Bool) : Structured.check (snapshot swapped) = .ok (program swapped) := by
  cases swapped <;> rfl

private def oracle : Oracle Id model.toCarriers Nat := fun _ event counter =>
  match event with
  | .challenge origin =>
      if h : origin.request = some (.draw "extension") then
        (.returned (by simpa [Raw, h, Request.draw, model] using (2 : ZMod 5)), counter + 1)
      else (.stopped .refused, counter)
  | _ => (.stopped .refused, counter)

private def state (env : Environment model.toCarriers := [])
    (proof : Proof model.toCarriers := []) : RuntimeState model.toCarriers Nat := ⟨env, proof, 0⟩

private def policy : Policy := ⟨"main", "P", "V", 0, "suite", [], [], [], "test", "test"⟩
private def constructed (instructions : List Instruction) (inputs outputs : List ValueSort)
    (returned : List Nat) : Participant :=
  ⟨"fixture", "fixture", policy, "fixture", inputs, outputs, instructions, returned⟩

private def message : Template :=
  ⟨"main", [], ["message", "main", "m", "m", "P", "V"]⟩
private def query : Template :=
  ⟨"main", [], ["query", "main", "q", "input_0", "random.extension/0", "draw", "V"]⟩
private def base (n : Int) : Value model.toCarriers := .data (.field "base" n)
private def extension (n : ZMod 5) : Value model.toCarriers := .data (.field "extension" n)

-- Distinct carrier types and nominal identities both survive decoding.
example (x : Int) : (base x).decode (.field "base") = some x := by rfl
example (x : ZMod 5) : (extension x).decode (.field "extension") = some x := by rfl
example (x : Int) : (base x).decode (.field "extension") = none := by simp [Domain.Value.decode, base, Domain.Payload.value]
example : Value.encode (carriers := model.toCarriers) (.service "random.extension/0") 0 = none := rfl
example : (Payload.index 0 : Payload model.toCarriers).value (.service "s") = none := rfl

example : calculate model (.fieldAdd "base") [base 4, base 7] = .returned [base 11] := by rfl
example : calculate model (.fieldAdd "extension") [extension 4, extension 3] =
    .returned [extension 2] := by rfl
example : calculate model (.fieldAdd "extension") [base 4, extension 3] = .stopped .refused := by rfl
example : calculate model (.boundedAt "base") [.data (.vector "base" [3]), .data (.index 4)] =
    .stopped .refused := by rfl

-- Lookup uses this exact admitted helper body and its entire declared signature.
example : callHelper model (program false) "pair" [.data .boolean, .data .boolean]
    [.data (.boolean true), .data (.boolean false)] =
    .returned [.data (.boolean true), .data (.boolean false)] := by rfl
example : callHelper model (program true) "pair" [.data .boolean, .data .boolean]
    [.data (.boolean true), .data (.boolean false)] =
    .returned [.data (.boolean false), .data (.boolean true)] := by rfl
example : callHelper model (program false) "pair" [.data .index, .data .index]
    [.data (.boolean true), .data (.boolean false)] = .stopped .refused := by rfl
example : callHelper model (program false) "missing" [] [] = .stopped .refused := by rfl
example : callHelper model (program false) "stop" [] [] = .stopped .abort := by rfl

private def producer : Participant := constructed
  [⟨.send "m" "m" "V", [0], [], []⟩,
   ⟨.observe "suite" message, [1, 0, 2], [.transcript "suite"], []⟩,
   ⟨.challenge "suite" "extension" query, [3, 2],
     [.data (.field "extension"), .transcript "suite"], []⟩]
  [.data (.field "base"), .transcript "suite", .indices]
  [.data (.field "base"), .data (.field "extension"), .transcript "suite"] [0, 4, 5]

private def validator : Participant := constructed
  [⟨.receive "m" "m" "P" (.field "base"), [], [.data (.field "base")], []⟩,
   ⟨.observe "suite" message, [0, 2, 1], [.transcript "suite"], []⟩,
   ⟨.challenge "suite" "extension" query, [3, 1],
     [.data (.field "extension"), .transcript "suite"], []⟩]
  [.transcript "suite", .indices]
  [.data (.field "base"), .data (.field "extension"), .transcript "suite"] [2, 4, 5]

private def generated := produce model (program false) context producer
  [base 7, .transcript "suite" [], .indices []] oracle 0
private def checked := validate model (program false) context validator
  [.transcript "suite" [], .indices []] generated.state.proof oracle generated.state.oracle

example : generated.state.proof = [.field "base" 7] := by rfl
example : generated.state.oracle = 1 := by rfl
example : checked.state.proof = [] := by rfl
example : checked.state.oracle = 2 := by rfl
example : generated.events = checked.events := by rfl
example : (match generated.outcome, checked.outcome with
    | .returned p, .returned v => p.values = v.values
    | _, _ => False) := by rfl
example : generated.state.environment.length = 6 := by rfl
example : (validate model (program false) context validator [.transcript "suite" [], .indices []]
    [.field "extension" 1] oracle 0).outcome = .stopped .refused := by rfl
example : (validate model (program false) context validator [.transcript "suite" [], .indices []]
    [.field "extension" 1] oracle 0).state.proof = [.field "extension" 1] := by rfl
example : (validate model (program false) context validator [.transcript "suite" [], .indices []]
    [.field "base" 7, .boolean false] oracle 0).state.proof = [.boolean false] := by rfl

-- Captured outer values, carried state, and induction coordinates in a small loop.
private def loopBody : List Instruction :=
  [⟨.calculate (.fieldAdd "base"), [1, 3], [.data (.field "base")], []⟩]
private def loopProgram (bound : Nat) : PIR.Process (effects model.toCarriers)
    (Environment model.toCarriers) :=
  evaluate model (program false) context
    [⟨.loop "loop" 3 [4], [0, 1], [.data (.field "base")], loopBody⟩]
    [.data (.index bound), base 2]
example : (run .validator oracle (loopProgram 3) (state [] [])).outcome =
    .returned [.data (.index 3), base 2, base 8] := by rfl
example : (run .validator oracle (loopProgram 0) (state [] [])).outcome =
    .returned [.data (.index 0), base 2, base 2] := by rfl
example : (run .validator oracle (loopProgram 4) (state [] [])).outcome = .stopped .refused := by rfl

-- Stops retain already generated proof and the environment at the failing step.
private def failAfterSend := evaluate model (program false) context
  [⟨.send "m" "m" "V", [0], [], []⟩, ⟨.guard "g", [1], [], []⟩]
  [base 7, .data (.boolean false)]
example : (run .producer oracle failAfterSend (state [] [])).outcome = .stopped .reject := by rfl
example : (run .producer oracle failAfterSend (state [] [])).state.proof = [.field "base" 7] := by rfl
example : (run .producer oracle failAfterSend (state [] [])).state.environment =
    [base 7, .data (.boolean false)] := by rfl

-- Malformed request/domain/method/template and unsupported private coins refuse.
example : queryOrigin { context with request := some (.draw "base") } "suite" "extension" query [] = none := by rfl
example : queryOrigin context "suite" "base" query [] = none := by rfl
example : queryOrigin { context with request := some ⟨"index", [], .field "extension"⟩ }
    "suite" "extension" query [] = none := by rfl
-- Runtime normalization reads the selected root service. Exact local port
-- identity is checked against source by SourceOccurrences before execution.
example : queryOrigin context "suite" "extension" { query with event :=
    ["query", "main", "q", "input_1", "random.extension/0", "draw", "V"] } [] =
    some (context.query "q" (.draw "extension")) := by rfl
example : (run .producer oracle (evaluate model (program false) context
    [⟨.unsupported "private_coins", [], [], []⟩] []) (state [] [])).outcome = .stopped .refused := by rfl

-- Sequencing uses the producer's exact proof and oracle post-state.
private def paired := executePair model (program false) context producer validator
  [base 7, .transcript "suite" [], .indices []] [.transcript "suite" [], .indices []] oracle 0
example : paired.producer.state.proof = [.field "base" 7] := by rfl
example : paired.validator = some checked := by rfl
private def failedProducer : Participant := constructed
  [⟨.send "m" "m" "V", [0], [], []⟩, ⟨.guard "g", [1], [], []⟩]
  [.data (.field "base"), .data .boolean] [] []
private def failedPair := executePair model (program false) context failedProducer validator
  [base 7, .data (.boolean false)] [] oracle 0
example : failedPair.producer.outcome = .stopped .reject := by rfl
example : failedPair.producer.state.proof = [.field "base" 7] := by rfl
example : failedPair.validator = none := by rfl

-- Data sorts beyond native scalar messaging have typed formal payloads.
example : (run .validator oracle (step model (program false) context
    ⟨.receive "v" "v" "P" (.vector "base"), [], [.data (.vector "base")], []⟩ [])
    (state [] [.vector "base" [1, 2]])).outcome =
    .returned [.data (.vector "base" [1, 2])] := by rfl
example : (run .validator oracle (step model (program false) context
    ⟨.receive "i" "i" "P" .index, [], [.data .index], []⟩ [])
    (state [] [.index 3])).outcome = .returned [.data (.index 3)] := by rfl
example : (run .validator oracle (step model (program false) context
    ⟨.receive "g" "g" "P" (.group "group"), [], [.data (.group "group")], []⟩ [])
    (state [] [.group "group" (3 : Int)])).outcome = .returned [.data (.group "group" (3 : Int))] := by rfl
example : (run .validator oracle (step model (program false) context
    ⟨.receive "s" "s" "P" (.service "s"), [], [.data (.service "s")], []⟩ [])
    (state [] [.index 3])).outcome = .stopped .refused := by rfl
example : (run .validator oracle (step model (program false) context
    ⟨.receive "m" "m" "P" .boolean, [], [.data .index], []⟩ [])
    (state [] [.boolean true])).state.proof = [.boolean true] := by rfl
example : (run .producer oracle (step model (program false) context
    ⟨.receive "m" "m" "V" .boolean, [], [.data .boolean], []⟩ [])
    (state [] [])).outcome = .stopped .refused := by rfl
example : queryOrigin context "suite" "extension" message [] = none := by rfl
example : templateOrigin context message [0] = none := by rfl
example : templateOrigin context { message with entry := "other" } [] = none := by rfl
-- Called protocols retain their own local event entry and service index. The
-- checked construction rule resolves those to the root service and qualified
-- site; equality of the local port with the root port is not required.
private def nestedMessage : Template :=
  ⟨"main", [⟨"apply", "main", "reduce"⟩],
    ["message", "Reduce", "m", "m", "P", "V"]⟩
private def nestedQuery : Template :=
  ⟨"main", [⟨"apply", "main", "reduce"⟩],
    ["query", "Reduce", "q", "input_5", "random.extension/0", "draw", "V"]⟩
example : templateOrigin context nestedMessage [] =
    some (.message "main" (nestedMessage.qualify "m") "P" "V") := by rfl
example : queryOrigin context "suite" "extension" nestedQuery [] =
    some (context.query (nestedQuery.qualify "q") (.draw "extension")) := by rfl
example : templateOrigin context { nestedMessage with
    event := ["message", "Reduce", "m", "wrong-schema", "P", "V"] } [] = none := by rfl
example : templateOrigin context { nestedQuery with
    event := ["query", "Reduce", "q", "input_5", "random.extension/0", "private-coins", "V"] }
    [] = none := by rfl
example : (run .validator oracle (step model (program false) context
    ⟨.indicesAppend, [0, 1], [.indices], []⟩ [.indices [], .data (.boolean true)])
    (state [] [])).outcome = .stopped .refused := by rfl
example : (run .validator oracle (step model (program false) context
    ⟨.observe "suite" message, [0, 1, 2], [.transcript "suite"], []⟩
      [.transcript "other" [], base 1, .indices []])
    (state [] [])).outcome = .stopped .refused := by rfl

-- The embedding operation is interpreted only through operationOn. These
-- operational fixtures intentionally provide no extension-field laws.
example : calculate model (.fieldEmbed "extension" "base") [base 7] =
    .returned [extension 0] := by rfl
example : calculate model (.fieldEmbed "extension" "base") [extension 1] =
    .stopped .refused := by rfl

end Tests.DomainExecution
