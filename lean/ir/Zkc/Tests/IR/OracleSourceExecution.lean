import Zkc.IR.Source.Structured.OracleIngress

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
namespace Tests.OracleSourceExecution

private abbrev model : DomainModel := ringModel Int Int
private abbrev baseKind : OracleKind := .table .index none
private abbrev virtualKind : OracleKind := .table .index (some 1)

private def predicate : Function :=
  ⟨"admissible", .math, .privateDef, [.indices], [.boolean], none, [], none,
    .block [.instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])⟩

private def declaration : OracleDeclaration :=
  ⟨"Pair", [.oracle baseKind, .index], virtualKind, "pair_admissible", [], [],
    .block [
      .instruction (.oracle (.query none baseKind)) [0, 1] [.index] [] "low",
      .instruction (.indexConstant "1") [] [.index] [] "",
      .instruction .indexWrappingAdd [3, 0] [.index] [] "",
      .instruction (.oracle (.query none baseKind)) [3, 0] [.index] [] "high",
      .instruction .indexWrappingAdd [3, 0] [.index] [] ""] (.ret [0])⟩

private def protocol (name : String) (inputs outputs : List Ty)
    (inputScopes outputScopes : List (List String)) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs, outputs,
    some ⟨["P", "V"], inputScopes, outputScopes⟩, [], some (.protocol ⟨name, []⟩), body⟩

private def child : Definition :=
  protocol "child" [.indices] [.index] [["P"]] [["V"]]
    (.block [
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.oracle (.send "P" ["V"] baseKind ["rows"] [("rows", 2)]))
        [1, 0] [.oracle baseKind] [] "base",
      .instruction (.oracle (.virtual "Pair" "P" ["V"] virtualKind))
        [0] [.oracle virtualKind] [] "",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.oracle (.query (some "V") virtualKind)) [1, 0] [.index] [] "query"]
      (.ret [0]))

private def root : Definition :=
  protocol "main" [.indices] [.index] [["P"]] [["V"]]
    (.block [
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.protocolRepeat 1 2 ["P", "V"] [["V"]]) [1, 0, 2] [.index]
        [.region [.index, .index, .indices] [.index]
          (.block [.instruction (.protocolApply "child" ["P", "V"]) [2] [.index] [] "child"]
            (.yield [0]))] "round"] (.ret [0]))

private def snapshot : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000", "main", [],
    [⟨"pair_admissible", .privateDef, "zkc.language.formula/0", "pair", "0",
      [.indices], [.boolean], ["parameter"], some "admissible", []⟩], [],
    [.function predicate, .oracle declaration, child, root],
    [⟨"child", []⟩, ⟨"main", []⟩], blsRows, {}⟩

private def provide (bad : Option Nat) (position state : Nat) (kind : OracleKind) :
    PIR.Execution Nat Nat (model.Value kind.answer) :=
  match kind with
    | .table .index _ =>
      if bad == some position then ⟨.stopped .abort, state + 1, [position]⟩
      else ⟨.returned (if position == 0 then (10 : Nat) else (20 : Nat)), state + 1, [position]⟩
    | _ => ⟨.stopped .refused, state, []⟩

private def base (bad : Option Nat) :
    PIR.Handler (oracleReadInterface model.toCarriers) Nat Nat :=
  fun request state ↦ provide bad request.position state request.kind

private def ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) Nat Nat :=
  fun _ state ↦ ⟨.stopped .refused, state, []⟩

private def childAt (rows position : Nat) : Definition :=
  protocol "child" [.indices] [.index] [["P"]] [["V"]]
    (.block [
      .instruction (.indexConstant (toString rows)) [] [.index] [] "",
      .instruction (.oracle (.send "P" ["V"] baseKind ["rows"] [("rows", 2)]))
        [1, 0] [.oracle baseKind] [] "base",
      .instruction (.oracle (.virtual "Pair" "P" ["V"] virtualKind))
        [0] [.oracle virtualKind] [] "",
      .instruction (.indexConstant (toString position)) [] [.index] [] "",
      .instruction (.oracle (.query (some "V") virtualKind)) [1, 0] [.index] [] "query"] (.ret [0]))

private def fields : ProductFields := .cons .indices (.cons .index .nil)
private def productType : Ty := .product "payload" "Payload" fields
private def projection : Definition := .function
  ⟨"project", .math, .privateDef, [productType], [.index], none, [], none,
    .block [.instruction (.getProduct 1) [0] [.index] [] ""] (.ret [0])⟩

private def lazyRoot (unusedQuery reject : Bool) : Definition :=
  let operations := [
    .instruction (.indexConstant "1") [] [.index] [] "",
    .instruction (.oracle (.send "P" ["V"] baseKind ["rows"] [("rows", 2)]))
      [1, 0] [.oracle baseKind] [] "base",
    .instruction (.oracle (.virtual "Pair" "P" ["V"] virtualKind))
      [0] [.oracle virtualKind] [] "",
    .instruction (.oracle (.contents "P" virtualKind)) [0] [.indices] [] "",
    .instruction (.indexConstant "7") [] [.index] [] "",
    .instruction (.makeProduct "Payload") [1, 0] [productType] [] "",
    .instruction (.call "project") [0] [.index] [] ""]
  let after := if unusedQuery then [
    .instruction (.indexConstant "0") [] [.index] [] "",
    .instruction (.oracle (.query (some "P") virtualKind)) [5, 0] [.index] [] "unused"]
    else if reject then [
      .instruction (.booleanConstant false) [] [.boolean] [] "",
      .instruction (.guard "P") [0] [] [] "unused_guard"] else []
  protocol "main" [.indices] [.index] [["P"]] [["P"]]
    (.block (operations ++ after) (.ret [if unusedQuery then 2 else if reject then 1 else 0]))

private def lazySnapshot (unusedQuery reject : Bool) : Snapshot :=
  {snapshot with definitions := [.function predicate, .oracle declaration, projection,
    lazyRoot unusedQuery reject], contracts := [⟨"main", []⟩]}

private def demandSnapshot : Snapshot :=
  match lazyRoot false false with
  | .function function =>
    let .block instructions _ := function.body
    let demand := {function with body := (.block
      (instructions ++ [.instruction (.exchange "P" "V") [3] [.indices] [] "demand"])
      (.ret [1]))}
    {snapshot with definitions := [.function predicate, .oracle declaration, projection,
      .function demand], contracts := [⟨"main", []⟩]}
  | _ => snapshot

private def optionalProjection : Definition := .function
  ⟨"optionalProject", .math, .privateDef, [.indices, .index], [.index], none, [], none,
    .block [.instruction (.indexConstant "99") [] [.index] [] ""] (.ret [2])⟩

private def optionalSnapshot : Snapshot :=
  {snapshot with definitions := [.function predicate, .oracle declaration, optionalProjection,
    protocol "main" [.indices] [.index] [["P"]] [["V"]]
      (.block [.instruction (.indexConstant "7") [] [.index] [] "",
        .instruction (.call "optionalProject") [1, 0] [.index] [] ""] (.ret [0]))], contracts := [⟨"main", []⟩]}

private def sequenceKind : OracleLogicalSort := .sequence virtualKind 2
private def sequenceFields : ProductFields := .cons (.sequence .indices) (.cons .index .nil)
private def sequenceProduct : Ty := .product "sequence_payload" "SequencePayload" sequenceFields
private def sequenceProjection : Definition := .function
  ⟨"sequenceProject", .math, .privateDef, [sequenceProduct], [.index], none, [], none,
    .block [.instruction (.getProduct 1) [0] [.index] [] ""] (.ret [0])⟩

private def sequenceEcho : Definition :=
  protocol "echo" [sequenceKind.dataType, sequenceKind.type]
    [sequenceKind.dataType, sequenceKind.type] [["P"], ["V"]] [["P"], ["V"]]
    (.block [
      .instruction (.oracle (.input "P" ["V"] sequenceKind.type [])) [0, 1]
        [sequenceKind.type] [] "",
      .instruction (.oracle (.components "P" ["V"] sequenceKind.type)) [0]
        [sequenceKind.dataType, sequenceKind.type] [] ""] (.ret [0, 1]))

private def sequenceRoot : Definition :=
  protocol "main" [.indices] [.index] [["P"]] [["P"]]
    (.block [
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.oracle (.send "P" ["V"] baseKind ["rows"] [("rows", 2)]))
        [1, 0] [.oracle baseKind] [] "base",
      .instruction (.oracle (.virtual "Pair" "P" ["V"] virtualKind))
        [0] [.oracle virtualKind] [] "",
      .instruction (.oracle (.sequenceEmpty virtualKind 2)) [] [sequenceKind.type] [] "",
      .instruction (.oracle (.sequenceAppend virtualKind 2 ["P", "V"])) [0, 1]
        [sequenceKind.type] [] "append",
      .instruction (.oracle (.components "P" ["V"] sequenceKind.type)) [0]
        [sequenceKind.dataType, sequenceKind.type] [] "",
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.protocolRepeat 2 2 ["P", "V"] [["P"], ["V"]]) [0, 1, 2]
        [sequenceKind.dataType, sequenceKind.type]
        [.region [.index, sequenceKind.dataType, sequenceKind.type]
          [sequenceKind.dataType, sequenceKind.type]
          (.block [.instruction (.protocolApply "echo" ["P", "V"]) [1, 2]
            [sequenceKind.dataType, sequenceKind.type] [] "echo"] (.yield [0, 1]))] "transport",
      .instruction (.indexConstant "7") [] [.index] [] "",
      .instruction (.makeProduct "SequencePayload") [1, 0] [sequenceProduct] [] "",
      .instruction (.call "sequenceProject") [0] [.index] [] ""] (.ret [0]))

private def sequenceSnapshot : Snapshot :=
  {snapshot with definitions := [.function predicate, .oracle declaration,
    sequenceProjection, sequenceEcho, sequenceRoot], contracts := [⟨"echo", []⟩, ⟨"main", []⟩]}

private def inputRoot : Definition :=
  protocol "main" [.indices, .oracle baseKind] [.index] [["P"], ["V"]] [["V"]]
    (.block [
      .instruction (.oracle (.input "P" ["V"] (.oracle baseKind) [("rows", 2)]))
        [0, 1] [.oracle baseKind] [] "",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.oracle (.query (some "V") baseKind)) [1, 0] [.index] [] "query"] (.ret [0]))

private def inputSnapshot : Snapshot :=
  {snapshot with definitions := [.function predicate, .oracle declaration, inputRoot], contracts := [⟨"main", []⟩]}

private def replace {V : Ty → Type} {types : List Ty} {type : Ty} :
    Values V types → Var types type → V type → Values V types
  | .cons _ rest, .here, value => .cons value rest
  | .cons head rest, .there position, value => .cons head (replace rest position value)

private def execute (source : Snapshot) (self : Nat) (data : Option (List Nat))
    (inspect : (program : Program) → (unit : CheckedOracleUnit) →
      PIR.Execution (OracleProtocol.State model unit.snapshot unit.domains unit.math Nat)
        (OracleProtocol.Event Nat)
        (Values (Component (ProtocolValue model.toCarriers)) program.payload.entry.outputs) → IO Unit) : IO Unit := do
  let imported : Imported source ← match admitted : check source with
    | .error code => throw (IO.userError ("source admission: " ++ code))
    | .ok program => pure ⟨program, admitted⟩
  let subject ← match imported.oracleSubject with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  let inputs : Values (Component model.Value) subject.imported.program.payload.entry.inputs :=
    Values.absent _ _
  let inputs := match Var.decode subject.imported.program.payload.entry.inputs .indices 0, data with
    | some binder, some data => replace inputs binder (some data)
    | _, _ => inputs
  let start ← match subject.start model self inputs [] (0 : Nat) with
    | .error code => throw (IO.userError ("source ingress: " ++ code))
    | .ok start => pure start
  let result := start.run ordinary (base none)
  have invariant : OracleProtocol.Reachable result.state := start.run_reachable ordinary (base none)
  let _ := invariant
  inspect subject.imported.program subject.unit result

private def sourceControls : IO Unit := do
  -- Pure constructions use structural occurrence identity; only visible effects
  -- and stopping checks carry authored sites in the native source contract.
  let .function childFunction := child | throw (IO.userError "child is not a function")
  let .block childInstructions childEnd := childFunction.body
  for (index, site, expected) in [(1, "", "structured-site"),
      (2, "invented_virtual_event", "oracle-protocol-unexpected-site"),
      (4, "", "structured-site")] do
    let body := .block (childInstructions.zipIdx.map fun
      (.instruction op args results regions oldSite, position) =>
        .instruction op args results regions (if position == index then site else oldSite)) childEnd
    let changed := {snapshot with definitions := [.function predicate, .oracle declaration,
      .function {childFunction with body := body}, root]}
    match check changed with
    | .error code => unless code == expected do
        throw (IO.userError s!"wrong site refusal at {index}: {code}")
    | .ok _ => throw (IO.userError s!"accepted malformed Oracle site at {index}")
  let .block instructions _ := declaration.body
  let changed := {declaration with body := .block instructions (.ret [1])}
  execute {snapshot with definitions := [.function predicate, .oracle changed, child, root]}
    1 none fun program _ result => do
      let .returned values := result.outcome | throw (IO.userError "changed source body stopped")
      let some binder := Var.decode program.payload.entry.outputs .index 0
        | throw (IO.userError "missing changed source result")
      unless (values.get binder).bind ProtocolValue.toConcrete == some 20 do
        throw (IO.userError "execution ignored its retained source body mutation")
      unless result.state.oracle.provider == 4 do
        throw (IO.userError "changed return erased unused retained reads")
  execute {snapshot with definitions := [.function predicate, .oracle declaration, childAt 2 1, root]}
    1 none fun _ _ result => do
      unless result.outcome matches .stopped .refused do throw (IO.userError "outer invalid read returned")
      unless result.state.oracle.queries == 1 && result.state.oracle.provider == 0 do
        throw (IO.userError "outer invalid read entered the virtual body")
  execute {snapshot with definitions := [.function predicate, .oracle declaration, childAt 1 0, root]}
    1 none fun _ _ result => do
      unless result.outcome matches .stopped .refused do throw (IO.userError "child invalid read returned")
      unless result.state.oracle.queries == 3 && result.state.oracle.provider == 1 do
        throw (IO.userError "child invalid read lost its reached prefix")
  execute (lazySnapshot false false) 0 (some [10]) fun program _ result => do
    let .returned values := result.outcome | throw (IO.userError "ignored deferred field was forced")
    let some binder := Var.decode program.payload.entry.outputs .index 0
      | throw (IO.userError "missing scalar result")
    unless (values.get binder).bind ProtocolValue.toConcrete == some 7 do
      throw (IO.userError "projection changed its selected field")
    unless result.state.oracle.queries == 0 && result.state.oracle.entries.length == 2 do
      throw (IO.userError "lazy product/helper demanded virtual data")
  execute (lazySnapshot true false) 0 (some [10]) fun _ _ result => do
    unless result.outcome matches .stopped .refused do throw (IO.userError "unused failed operation erased")
    unless result.state.oracle.queries == 3 && result.state.oracle.provider == 1 do
      throw (IO.userError "unused failed operation changed ordered reads")
  execute (lazySnapshot false true) 0 (some [10]) fun _ _ result => do
    unless result.outcome matches .stopped .reject do throw (IO.userError "zero-result stop erased")
    unless result.state.oracle.entries.length == 2 do throw (IO.userError "reject lost constructions")
  execute demandSnapshot 0 (some [10]) fun _ _ result => do
    unless result.outcome matches .stopped .refused do
      throw (IO.userError "concrete virtual demand invented contents")
    let locations := result.events.filterMap fun event ↦ match event with
      | .logical (.refusal location _) => some location.row
      | _ => none
    unless locations == [[7, 1, 7]] do
      throw (IO.userError s!"strict demand lost its reached source operation: {locations}")
    unless result.state.oracle.queries == 0 && result.state.oracle.entries.length == 2 do
      throw (IO.userError "concrete demand changed the retained store/read prefix")
  execute optionalSnapshot 1 none fun program _ result => do
    let .returned values := result.outcome | throw (IO.userError "unused optional input was demanded")
    let some binder := Var.decode program.payload.entry.outputs .index 0
      | throw (IO.userError "missing optional projection result")
    unless (values.get binder).bind ProtocolValue.toConcrete == some 7 do
      throw (IO.userError "ordinary optional helper changed its selected input")
  execute sequenceSnapshot 0 (some [10, 20]) fun program _ result => do
    let .returned values := result.outcome | throw (IO.userError "lazy sequence transport stopped")
    let some binder := Var.decode program.payload.entry.outputs .index 0
      | throw (IO.userError "missing sequence projection result")
    unless (values.get binder).bind ProtocolValue.toConcrete == some 7 do
      throw (IO.userError "sequence/record projection changed its field")
    unless result.state.oracle.queries == 0 && result.state.oracle.entries.length == 2 &&
        result.state.parents.isEmpty do throw (IO.userError "sequence transport forced data or lost frames")
  IO.println "oracle-source-controls: retained body mutation, outer/child invalid positions, lazy projection, unused failed operation, zero-result stop, located strict demand and lazy sequence/record application/repeat transport passed"

private def ingressControls : IO Unit := do
  let imported : Imported inputSnapshot ← match admitted : check inputSnapshot with
    | .error code => throw (IO.userError ("input admission: " ++ code))
    | .ok program => pure ⟨program, admitted⟩
  let subject ← match imported.oracleSubject with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  let types := subject.imported.program.payload.entry.inputs
  let some dataPort := Var.decode types .indices 0 | throw (IO.userError "missing input data")
  let some handlePort := Var.decode types (.oracle baseKind) 1 | throw (IO.userError "missing input anchor")
  let root := subject.unit.snapshot.definitions.findIdx (·.name == subject.unit.snapshot.entry)
  let anchor : OracleAnchor := ⟨⟨root, []⟩, .input 1⟩
  let absent : Values (Component model.Value) types := Values.absent _ _
  let receiverInputs := replace absent handlePort (some anchor)
  let receiver ← match subject.start model 1 receiverInputs [2] (0 : Nat) with
    | .error code => throw (IO.userError ("receiver ingress: " ++ code))
    | .ok start => pure start
  let result := receiver.run ordinary (base none)
  unless result.outcome matches .returned _ do throw (IO.userError "root binding did not execute")
  unless result.state.oracle.entries.length == 1 && result.state.oracle.provider == 1 do
    throw (IO.userError "root binding replaced the constructed input store")
  let holderInputs := replace absent dataPort (some [10, 20])
  unless (subject.start model 0 holderInputs [2] (0 : Nat)).isOk do
    throw (IO.userError "holder ingress rejected its source input")
  let wrong : OracleAnchor := ⟨⟨root, []⟩, .input 0⟩
  unless !(subject.start model 1 (replace absent handlePort (some wrong)) [2] (0 : Nat)).isOk do
    throw (IO.userError "unrelated root anchor admitted")
  unless !(subject.start model 0 holderInputs [1] (0 : Nat)).isOk do
    throw (IO.userError "mismatched holder shape admitted")
  IO.println "oracle-source-ingress: canonical source pair, holder shape and wrong-anchor rejection passed"

private def run : IO Unit := do
  let imported : Imported snapshot ← match admitted : check snapshot with
    | .error code => throw (IO.userError ("source admission: " ++ code))
    | .ok program => pure ⟨program, admitted⟩
  let subject ← match imported.oracleSubject with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  let inputs : Values (Component model.Value) subject.imported.program.payload.entry.inputs :=
    Values.absent _ _
  let start ← match subject.start model 1 inputs [] (0 : Nat) with
    | .error code => throw (IO.userError code)
    | .ok start => pure start
  let result := start.run ordinary (base none)
  let .returned values := result.outcome | throw (IO.userError "nested source computation stopped")
  let some output := Var.decode subject.imported.program.payload.entry.outputs .index 0
    | throw (IO.userError "missing nested computation output")
  unless (values.get output).bind ProtocolValue.toConcrete == some 30 do
    throw (IO.userError "nested source computation changed its answer")
  let trace := result.events.filterMap fun event ↦ match event with
    | .logical (.provider position) => some position | _ => none
  unless trace == [0, 1, 0, 1] do throw (IO.userError s!"wrong source read trace: {trace}")
  unless result.state.oracle.provider == 4 && result.state.oracle.queries == 6 do
    throw (IO.userError "wrong source query/poststate")
  unless result.state.oracle.entries.length == 4 && result.state.parents.isEmpty do
    throw (IO.userError "wrong source construction/frame count")
  let anchors := result.state.oracle.entries.map (·.2.anchor)
  unless anchors.eraseDups.length == 4 do throw (IO.userError "construction anchors collided")
  let stopped := start.run ordinary (base (some 1))
  unless stopped.outcome matches .stopped .abort do throw (IO.userError "lost source abort")
  unless stopped.state.oracle.provider == 2 && stopped.state.parents.length == 2 do
    throw (IO.userError "lost stopped provider/invocation state")
  let changed := {snapshot with definitions := snapshot.definitions ++
    [.oracle {declaration with name := "Dormant", body := .block [] (.ret [99])}]}
  unless !(check changed).isOk do throw (IO.userError "dormant declaration not checked")
  IO.println "oracle-source-execution: nested source application/repeat, immutable constructions, ordered expansion and abort controls passed"

#eval run
#eval sourceControls
#eval ingressControls
end Tests.OracleSourceExecution
