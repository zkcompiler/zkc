import Zkc.Source.Structured.OracleIngress
import Zkc.Source.Structured.CommonCoordinateSoundness

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured CommonCoordinate
namespace Tests.OracleCommonCoordinateControls

private abbrev model : DomainModel := ringModel Int Int
private def kind : OracleKind := .table .index none
private def pv : List String := ["P", "V"]

private def protocol (name : String) (inputs : List Ty) (scopes : List (List String))
    (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs, [],
    some ⟨pv, scopes, []⟩, [], some (.protocol ⟨name, []⟩), body⟩

private def snapshot (definitions : List Definition) : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000",
    "main", [], [], [], definitions,
    definitions.filterMap (fun definition ↦ match definition with
      | .function function => if function.kind == .protocol then some ⟨function.name, []⟩ else none
      | _ => none), blsRows, {}⟩

private def choose (name : String) (selected : List String := pv) : Definition :=
  protocol name [.index] [selected] (.block [
    .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
    .instruction (.oracle (.sequenceAt kind 2 selected)) [0, 1] [.oracle kind] [] "choose"]
    (.ret []))

private def literal : Definition := protocol "main" [] [] (.block [
  .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
  .instruction (.indexConstant "0") [] [.index] [] "",
  .instruction (.oracle (.sequenceAt kind 2 pv)) [1, 0] [.oracle kind] [] "choose"] (.ret []))

private def disagreement (separateInputs : Bool) : Definition :=
  let inputs := if separateInputs then [.index, .index] else []
  let initialOperations := if separateInputs then [] else [
    .instruction (.indexConstant "0") [] [.index] [] "",
    .instruction (.indexConstant "1") [] [.index] [] ""]
  protocol "main" inputs (inputs.map (fun _ ↦ pv)) (.block (initialOperations ++ [
    .instruction (.assemble pv) [0, 1] [.index] [] "",
    .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
    .instruction (.oracle (.sequenceAt kind 2 pv)) [0, 1] [.oracle kind] [] "choose"]) (.ret []))

private def localFunction : Definition := .function
  ⟨"opaque", .local, .privateDef, [.index], [.index], none, [], some (.local "opaque" []),
    .block [] (.ret [0])⟩

private def opaqueChoice (selected : List String) : Definition :=
  protocol "main" [] [] (.block [
    .instruction (.indexConstant "0") [] [.index] [] "",
    .instruction (.localCall "opaque" "P") [0] [.index] [] "local",
    .instruction (.exchange "P" "V") [0] [.index] [] "message",
    .instruction (.assemble pv) [1, 0] [.index] [] "",
    .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
    .instruction (.oracle (.sequenceAt kind 2 selected)) [0, 1] [.oracle kind] [] "choose"]
    (.ret []))

private def missingCommon : Definition := protocol "main" [.index] [["P"]] (.block [
  .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
  .instruction (.oracle (.sequenceAt kind 2 pv)) [0, 1] [.oracle kind] [] "choose"] (.ret []))

private def carried : Definition := protocol "main" [] [] (.block [
  .instruction (.indexConstant "0") [] [.index] [] "",
  .instruction (.indexConstant "1") [] [.index] [] "",
  .instruction (.protocolRepeat 1 1 pv [pv]) [0, 1] [.index]
    [.region [.index, .index] [.index] (.block [
      .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
      .instruction (.oracle (.sequenceAt kind 2 pv)) [0, 2] [.oracle kind] [] "choose"]
      (.yield [3]))] "round"] (.ret []))

private def nested : Snapshot := snapshot [choose "choose", protocol "middle" [.index] [pv]
  (.block [
    .instruction (.indexConstant "2") [] [.index] [] "",
    .instruction (.protocolRepeat 0 2 pv []) [0, 1] []
      [.region [.index, .index] [] (.block [
        .instruction (.indexConstant "2") [] [.index] [] "",
        .instruction (.protocolRepeat 0 2 pv []) [0, 1, 2] []
          [.region [.index, .index, .index] [] (.block [
            .instruction (.indexConstant "1") [] [.index] [] "",
            .instruction .indexWrappingAdd [1, 0] [.index] [] "",
            .instruction .indexWrappingAdd [0, 4] [.index] [] "",
            .instruction (.protocolApply "choose" ["V", "P"]) [0] [] [] "nested_choice"] (.yield []))]
          "inner"] (.yield []))] "outer"] (.ret [])),
  protocol "main" [.index] [pv] (.block [
    .instruction (.protocolApply "middle" pv) [0] [] [] "application"] (.ret []))]

private def select (source : Snapshot) : Except String (OracleSubject source) := do
  match admitted : check source with
  | .error code => throw code
  | .ok program => Imported.oracleSubject (⟨program, admitted⟩ : Imported source)

private def expect (label : String) (source : Snapshot) (allowed : Bool)
    (diagnostic : String := "") : IO Unit := do
  match select source with
  | .ok subject =>
    unless allowed do throw (IO.userError (label ++ ": unexpectedly admitted"))
    let selections := subject.coordinates.selections
    IO.println (label ++ ": admitted; selections=" ++ toString selections.length)
    for (_, selection) in selections do
      IO.println ("  " ++ toString selection.location.definition ++ ":" ++
        toString selection.location.row ++ " " ++ reprStr selection.requirements)
  | .error code =>
    if allowed || (!diagnostic.isEmpty && !(code.startsWith diagnostic)) then
      throw (IO.userError (label ++ ": " ++ code))
    IO.println (label ++ ": refused " ++ code)

#eval expect "literal" (snapshot [literal]) true
#eval expect "common input" (snapshot [choose "main"]) true
#eval expect "nested independent protocol" nested true
#eval expect "available divergent constants" (snapshot [disagreement false]) false
  "oracle-common-coordinate-opaque:definition=0:row=[7, 1, 4]"
#eval expect "different same-typed source roots" (snapshot [disagreement true]) false
  "oracle-common-coordinate-opaque"
#eval expect "opaque adversarial coordinate" (snapshot [localFunction, opaqueChoice pv]) false
  "oracle-common-coordinate-opaque"
#eval expect "role-local opaque coordinate" (snapshot [localFunction, opaqueChoice ["V"]]) true
#eval expect "single selected role" (snapshot [choose "main" ["V"]]) true

#eval expect "missing common input scope" (snapshot [missingCommon]) false "oracle-availability-input"
#eval expect "carried coordinate lacks step invariant" (snapshot [carried]) false
  "oracle-common-coordinate-opaque:definition=0:row=[7, 1, 2, 4, 0, 3, 1, 1]"

private def dormantBad : Definition := match disagreement false with
  | .function function => .function {function with
      name := "dormant", origin := some (.protocol ⟨"dormant", []⟩)}
  | definition => definition
#eval expect "dormant disagreement is checked" (snapshot [dormantBad, literal]) false
  "oracle-common-coordinate-opaque:definition=0:row=[7, 1, 4]"

private def bounded : IO Unit := do
  let source := snapshot [literal]
  let subject ← match select source with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  for (budget, expected) in [
      (({operations := 0} : Availability.Budget), "structured-availability-operation-limit"),
      (({dependencies := 0} : Availability.Budget), "structured-availability-dependency-limit"),
      (({replay := 0} : Availability.Budget), "structured-availability-replay-limit")] do
    match certify source subject.imported.program.payload.protocols budget with
    | .ok _ => throw (IO.userError "budget was ignored")
    | .error code =>
      unless code == expected do throw (IO.userError code)
      IO.println ("certificate budget: " ++ code)
#eval bounded

private def ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) Nat Nat :=
  fun _ state ↦ ⟨.stopped .refused, state, []⟩
private def base : PIR.Handler (oracleReadInterface model.toCarriers) Nat Nat :=
  fun _ state ↦ ⟨.stopped .refused, state, []⟩

private def execute (self : Nat) (value : Option Nat) : IO Unit := do
  let source := snapshot [choose "main" ["V"]]
  let subject ← match select source with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  let inputs : Values (Component model.Value) subject.imported.program.payload.entry.inputs :=
    Values.absent _ _
  let some port := Var.decode subject.imported.program.payload.entry.inputs .index 0
    | throw (IO.userError "entry input disappeared")
  let inputs := OracleIngress.replace inputs port value
  let start ← match subject.start model self inputs [] (0 : Nat) with
    | .error code => throw (IO.userError code)
    | .ok start => pure start
  let result := start.run ordinary base
  if self == 0 then
    unless result.outcome matches .returned _ do
      throw (IO.userError "unselected role changed behavior")
  else if value.isNone then
    unless result.outcome matches .stopped .incomplete do
      throw (IO.userError "absent coordinate did not stop incomplete")
  else
    unless result.outcome matches .stopped .refused do
      throw (IO.userError "empty sequence did not stop refused")
  unless result.state.oracle.provider == 0 && result.state.oracle.queries == 0 &&
      result.state.oracle.entries.isEmpty do
    throw (IO.userError "coordinate selection changed ingress/store accounting")
  let marks := result.events.filterMap fun event ↦ match event with
    | .mark site => some site
    | _ => none
  unless marks == ["", "choose"] do
    throw (IO.userError ("source prefix changed: " ++ toString marks))
  IO.println ("role=" ++ toString self ++ "; present=" ++ toString value.isSome ++
    "; exact source prefix; events=" ++ toString result.events.length)

#eval execute 0 none
#eval execute 1 none
#eval execute 1 (some 0)

private def singleSuccess : Definition := protocol "main" [.indices] [["P"]] (.block [
  .instruction (.indexConstant "1") [] [.index] [] "",
  .instruction (.oracle (.send "P" ["V"] kind ["rows"] [("rows", 1)]))
    [1, 0] [.oracle kind] [] "send",
  .instruction (.oracle (.sequenceEmpty kind 2)) [] [.oracleSequence kind 2] [] "",
  .instruction (.oracle (.sequenceAppend kind 2 ["V"])) [0, 1] [.oracleSequence kind 2] [] "append",
  .instruction (.indexConstant "0") [] [.index] [] "",
  .instruction (.oracle (.sequenceAt kind 2 ["V"])) [1, 0] [.oracle kind] [] "choose"] (.ret []))

private def executeSuccess (self : Nat) : IO Unit := do
  let source := snapshot [singleSuccess]
  let subject ← match select source with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  let some port := Var.decode subject.imported.program.payload.entry.inputs .indices 0
    | throw (IO.userError "entry input disappeared")
  let inputs := OracleIngress.replace (Values.absent _ _) port
    (if self == 0 then some [7] else none)
  let start ← match subject.start model self inputs [] (0 : Nat) with
    | .error code => throw (IO.userError code)
    | .ok start => pure start
  let result := start.run ordinary base
  unless result.outcome matches .returned _ do
    throw (IO.userError "legitimate single-role family selection stopped")
  unless result.state.oracle.provider == 0 && result.state.oracle.queries == 0 &&
      result.state.oracle.entries.length == 1 do
    throw (IO.userError "single-role family store accounting changed")
  let marks := result.events.filterMap fun event ↦ match event with
    | .mark site => some site
    | _ => none
  unless marks == ["", "send", "", "append", "", "choose"] do
    throw (IO.userError "single-role source prefix changed")
  IO.println ("one-role selection succeeds; self=" ++ toString self ++
    "; one source table; zero queries; exact source marks")

#eval executeSuccess 0
#eval executeSuccess 1

end Tests.OracleCommonCoordinateControls
