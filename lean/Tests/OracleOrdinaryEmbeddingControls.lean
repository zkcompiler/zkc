module

public import Tests.OracleOrdinaryEmbedding
meta import Tests.OracleOrdinaryEmbedding

@[expose] public section

/-! Complete retained-source controls, with the original Region and lazy Oracle
instance. Synthetic snapshots are labeled; generated service snapshots are reused
unchanged. Runtime controls supplement the generic all-input kernel theorem. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Tests.OracleOrdinaryEmbedding.Controls
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.ProtocolEmbedding

abbrev model : DomainModel := ringModel Int Int

def protocol (name : String) (inputs outputs : List Ty)
    (inputScopes outputScopes : List (List String)) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs, outputs,
    some ⟨["P", "V"], inputScopes, outputScopes⟩, [], some (.protocol ⟨name, []⟩), body⟩

def source (definitions : List Definition) : Snapshot :=
  { Scalar.snapshot with
    source := "sha256:" ++ String.ofList (List.replicate 64 '0')
    entry := "main"
    definitions := definitions
    contracts := definitions.filterMap fun
      | .function function =>
          if function.kind == .protocol then some ⟨function.name, []⟩ else none
      | _ => none }

def optionalSource : Snapshot := source [
  .function ⟨"project", .math, .privateDef, [.indices, .index], [.index], none, [], none,
    .block [.instruction (.indexConstant "99") [] [.index] [] ""] (.ret [2])⟩,
  protocol "main" [.indices] [.index] [["P"]] [["V"]]
    (.block [.instruction (.indexConstant "7") [] [.index] [] "",
      .instruction (.call "project") [1, 0] [.index] [] ""] (.ret [0]))]

def nestedSource (reject : Bool) : Snapshot := source [
  .function ⟨"increment", .math, .privateDef, [.index], [.index], none, [], none,
    .block [.instruction (.indexConstant "1") [] [.index] [] "",
      .instruction .indexWrappingAdd [1, 0] [.index] [] ""] (.ret [0])⟩,
  protocol "advance" [.index] [.index] [["P"]] [["P"]]
    (.block ([.instruction (.call "increment") [0] [.index] [] ""] ++
      if reject then [.instruction (.booleanConstant false) [] [.boolean] [] "",
        .instruction (.guard "P") [0] [] [] "reject"] else []) (.ret [if reject then 1 else 0])),
  protocol "main" [] [.index] [] [["P"]]
    (.block [
      .instruction (.indexConstant "2") [] [.index] [] "",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.protocolRepeat 1 2 ["P", "V"] [["P"]]) [1, 0] [.index]
        [.region [.index, .index] [.index]
          (.block [.instruction (.indexConstant "3") [] [.index] [] "",
            .instruction (.protocolRepeat 1 3 ["P", "V"] [["P"]]) [0, 2] [.index]
              [.region [.index, .index] [.index]
                (.block [.instruction (.protocolApply "advance" ["P", "V"]) [1]
                  [.index] [] "advance"] (.yield [0]))] "inner"] (.yield [0]))] "outer"]
      (.ret [0]))]

/-- A dormant, source-retained partial Math helper. Its external bound premise is
formation metadata; the embedding of its actual body covers even invalid inputs. -/
def boundedSource : Snapshot := source [
  .function ⟨"read", .math, .privateDef,
    [.vector "koala-bear", .index], [.field "koala-bear"], none, [⟨1, 0, 0⟩], none,
    .block [.instruction (.boundedAt "koala-bear") [0, 1] [.field "koala-bear"] [] ""]
      (.ret [0])⟩,
  protocol "main" [] [] [] [] (.block [] (.ret []))]

def oracleSource : Snapshot := source [
  protocol "main" [.indices] [.oracle (.table .index none)] [["P"]] [["V"]]
    (.block [.instruction (.indexConstant "1") [] [.index] [] "",
      .instruction (.oracle (.send "P" ["V"] (.table .index none) ["rows"] [("rows", 2)]))
        [1, 0] [.oracle (.table .index none)] [] "base"] (.ret [0]))]

/-- Every public action is refused by this control handler. Pure source controls
must finish or stop before any such action; no fabricated mathematical callback is used. -/
def refuse : PIR.Handler (OracleProtocol.Interface model) Nat String :=
  fun _ state ↦ ⟨.stopped .abort, state + 1, ["unexpected-public-action"]⟩

def indexResult {ts : List Ty} : Values (Component model.Value) ts → Option Nat
  | .nil => none
  | @Values.cons _ _ .index _ value _ => value
  | .cons _ _ => none

def lazyIndexResult {ts : List Ty} (result : PIR.Outcome
    (Values (Component (ProtocolValue model.toCarriers)) ts)) : Option Nat :=
  match result with
  | .stopped _ => none
  | .returned values => indexResult (ProtocolValue.concreteComponents values)

def stopped {A : Type} (reason : PIR.Stop) : PIR.Outcome A → Bool
  | .stopped actual => actual == reason
  | _ => false

private def run : IO Unit := do
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    unless ok do throw (IO.userError s!"ordinary lazy embedding control: {name}")
    count.modify (· + 1)
  for (name, snapshot) in [("optional", optionalSource), ("nested", nestedSource false),
      ("reject", nestedSource true), ("bounded", boundedSource)] do
    let program ← match Structured.check snapshot with
      | .ok program => pure program
      | .error error => throw (IO.userError s!"ordinary synthetic admission {name}: {error}")
    test "whole exact closure ordinary" (checkOrdinaryFragment program.payload)
    test "ordinary source selection" (!snapshot.requiresOracleRuntime)
    if program.payload.entry.inputs == [.indices] then
      let inputs := Values.absent model.Value program.payload.entry.inputs
      let execution := ((program.oracleParticipant model 1
        (ProtocolValue.embedComponents inputs)).interpret
        (eraseInternal model.toCarriers)).run refuse 41
      test "ignored absent optional operand returns original scalar"
        (lazyIndexResult execution.outcome == some 7)
      test "ignored argument makes no public request"
        (execution.state == 41 && execution.events.isEmpty)
    else if program.payload.entry.outputs == [.index] then
      let inputs := Values.absent model.Value program.payload.entry.inputs
      let execution := ((program.oracleParticipant model 0
        (ProtocolValue.embedComponents inputs)).interpret
        (eraseInternal model.toCarriers)).run refuse 41
      if name == "reject" then
        test "zero-result guard rejects inside nested callbacks" (stopped .reject execution.outcome)
      else
        test "nested repeat and retained helper give six"
          (lazyIndexResult execution.outcome == some 6)
      test "bookkeeping is not a public event" (execution.state == 41 && execution.events.isEmpty)
    else
      let helper : Helper := ⟨"read", .math, [.vector "koala-bear", .index], [.field "koala-bear"]⟩
      let args : Values (Component model.Value) helper.inputs :=
        .cons (some []) (.cons (some 0) .nil)
      let lazy := invoke (program.payload.oracleCalculations model 0) helper
        (ProtocolValue.embedComponents args)
      let ordinary := invoke (ordinaryTables program.payload model).components helper args
      test "retained bounded read fails on empty actual vector"
        (stopped .refused (lazy.run refuse 41).outcome)
      test "original bounded read retains the same failure"
        (stopped .refused (ordinary.run refuse 41).outcome)
  let .ok oracle := Structured.check oracleSource
    | throw (IO.userError "Oracle negative control must be admitted")
  test "Oracle-bearing source cannot obtain ordinary fragment"
    (!checkOrdinaryFragment oracle.payload)
  test "Oracle-bearing source cannot use ordinary source guard" oracleSource.requiresOracleRuntime
  test "ordinary witness checker refuses the Oracle source"
    (match checkOrdinarySource oracleSource with
    | .error "ordinary-embedding-oracle-source" => true
    | _ => false)
  let inputs := Values.absent model.Value oracle.payload.entry.inputs
  let old := (oracle.participantOn model 1 inputs).interpret (OracleProtocol.actions model)
  let lazy := (oracle.oracleParticipant model 1 (ProtocolValue.embedComponents inputs)).interpret
    (eraseInternal model.toCarriers)
  test "old Oracle refusal is not lazy Oracle semantics"
    (stopped .refused (old.run refuse 41).outcome &&
      stopped .abort (lazy.run refuse 41).outcome && (lazy.run refuse 41).state == 42)
  IO.println s!"oracle-ordinary-embedding: {← count.get} source controls passed"

#eval run
end Tests.OracleOrdinaryEmbedding.Controls

namespace Tests.OracleOrdinaryEmbedding.Controls
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.ProtocolEmbedding

abbrev field := "koala-bear.ext4-binomial3"
abbrev contract := "random.koala-bear.ext4-binomial3/0"

def sigmaSource : Snapshot := source [
  protocol "main" [.service contract, .field field, .field field] [.field field]
    [["P"], ["P"], ["P"]] [["P"]]
    (.block [.instruction (.draw "P" field) [0] [.field field] [] "challenge",
      .instruction (.fieldMultiply field) [0, 3] [.field field] [] "",
      .instruction (.fieldAdd field) [0, 3] [.field field] [] ""] (.ret [0]))]

/-- Requests are recorded with their exact handle, dynamic bound and block count.
The control returns arbitrary, possibly invalid, replies before source validation. -/
def replies (scalar : Nat) (block : List Nat) (challenge : Int)
    (failure : Option PIR.Stop := none) :
    PIR.Handler (OracleProtocol.Interface model) Nat String :=
  fun action state ↦ match action with
  | .ordinary (.query site operation args) =>
    let event := match operation, args with
      | .draw _, .cons handle .nil => s!"draw:{site}:{handle}"
      | .sampleIndex _, .cons handle (.cons bound .nil) => s!"index:{site}:{handle}:{bound}"
      | .sampleIndices _, .cons handle (.cons bound (.cons count .nil)) =>
        s!"block:{site}:{handle}:{bound}:{count}"
    match failure with
    | some why => ⟨.stopped why, state + 1, [event]⟩
    | none => match operation with
      | .draw _ => ⟨.returned challenge, state + 1, [event]⟩
      | .sampleIndex _ => ⟨.returned scalar, state + 1, [event]⟩
      | .sampleIndices _ => ⟨.returned block, state + 1, [event]⟩
  | .ordinary (.send site _ _) => ⟨.returned (), state + 1, [s!"send:{site}"]⟩
  | .ordinary (.receive type site _) => match type with
    | .index => ⟨.returned scalar, state + 1, [s!"receive:{site}"]⟩
    | _ => ⟨.stopped .refused, state + 1, [s!"receive:{site}"]⟩
  | _ => ⟨.stopped .refused, state + 1, ["unexpected"]⟩

def scalarResult {ts : List Ty} : Values (Component model.Value) ts → Option Int
  | .nil => none
  | @Values.cons _ _ (.field _) _ value _ => value
  | .cons _ _ => none

private def runServices : IO Unit := do
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    unless ok do throw (IO.userError s!"ordinary lazy service control: {name}")
    count.modify (· + 1)
  for (name, snapshot) in [("scalar", Scalar.snapshot), ("block", Block.snapshot),
      ("repeated", Repeated.snapshot)] do
    let .ok program := Structured.check snapshot | throw (IO.userError "generated source admission")
    test "exact generated service source fragment" (checkOrdinaryFragment program.payload)
    if signature : program.payload.entry.inputs = [.service contract] then
      let inputs : Values (Component model.Value) program.payload.entry.inputs :=
        signature.symm ▸ (.cons (some 17) .nil : Values (Component model.Value) [.service contract])
      let execute (scalar : Nat) (block : List Nat) (failure : Option PIR.Stop) :=
        ((program.oracleParticipant model 1 (ProtocolValue.embedComponents inputs)).interpret
          (eraseInternal model.toCarriers)).run (replies scalar block 3 failure) 41
      let result := execute 3 [3, 2, 1] none
      let expected := if name == "block" then
        ["block:label_706f736974696f6e73:17:8:3", "send:label_64656c6976657279_0"]
        else if name == "repeated" then [] else
        ["index:label_706f736974696f6e:17:8", "send:label_64656c6976657279_0"]
      if name == "repeated" then
        test "repeated typed request count and public history" (result.state == 47 &&
          result.events == List.flatten (List.replicate 3
            ["index:label_706f736974696f6e:17:8", "send:label_64656c6976657279_0"]))
        let late : PIR.Handler (OracleProtocol.Interface model) Nat String := fun action state ↦
          replies 3 [3, 2, 1] 3 (if state == 43 then some .reject else none) action state
        let partialExecution := ((program.oracleParticipant model 1
          (ProtocolValue.embedComponents inputs)).interpret
            (eraseInternal model.toCarriers)).run late 41
        test "callback stop preserves earlier requests and sends"
          (stopped .reject partialExecution.outcome && partialExecution.state == 44 &&
            partialExecution.events == ["index:label_706f736974696f6e:17:8",
            "send:label_64656c6976657279_0", "index:label_706f736974696f6e:17:8"])
      else test "exact scalar/block request values and ordered history" (result.events == expected)
      for reason in [PIR.Stop.abort, .reject, .refused, .incomplete, .exhausted] do
        let failed := execute 3 [3, 2, 1] (some reason)
        test "every provider stop retains reached state and single request"
          (stopped reason failed.outcome && failed.state == 42 && failed.events.length == 1)
      let invalid := if name == "block" then execute 3 [3, 2] none else execute 8 [] none
      test "invalid typed reply refuses before send or next iteration"
        (stopped .refused invalid.outcome && invalid.state == 42 && invalid.events.length == 1)
    else throw (IO.userError "generated service ABI changed")
  let .ok privateServices := Structured.check Local.snapshot
    | throw (IO.userError "generated private-service source admission")
  if signature : privateServices.payload.entry.inputs =
      [.service contract, .service contract, .service contract] then
    let inputs : Values (Component model.Value) privateServices.payload.entry.inputs :=
      signature.symm ▸
      (.cons (some 11) (.cons (some 13) (.cons (some 17) .nil)) :
        Values (Component model.Value) [.service contract, .service contract, .service contract])
    let execute (self : Nat) := ((privateServices.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers)).run
        (replies 2 [2, 1] 3) 41
    test "producer private scalar and block keep exact capability and scopes"
      ((execute 0).events == ["index:s0:11:3", "block:s2:11:3:2",
        "receive:label_64656c6976657279_0"])
    test "verifier private and public scalar requests keep different handles"
      ((execute 1).events == ["index:s4:13:3", "index:label_706f736974696f6e:17:8",
        "send:label_64656c6976657279_0"])
  else throw (IO.userError "generated private-service ABI changed")
  let .ok sigma := Structured.check sigmaSource
    | throw (IO.userError "scalar service source admission")
  test "scalar arithmetic with private service fragment" (checkOrdinaryFragment sigma.payload)
  if signature : sigma.payload.entry.inputs = [.service contract, .field field, .field field] then
    let inputs : Values (Component model.Value) sigma.payload.entry.inputs := signature.symm ▸
      (.cons (some 19) (.cons (some 7) (.cons (some 5) .nil)) :
        Values (Component model.Value) [.service contract, .field field, .field field])
    let result := ((sigma.oracleParticipant model 0
      (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers)).run (replies 0 [] 3) 41
    test "private draw preserves exact capability and site" (result.events == ["draw:challenge:19"])
    test "scalar response retains original arithmetic" (match result.outcome with
      | .returned values => scalarResult (ProtocolValue.concreteComponents values) == some 22
      | _ => false)
  else throw (IO.userError "scalar ABI changed")
  IO.println s!"oracle-ordinary-embedding: {← count.get} service controls passed"

#eval runServices
end Tests.OracleOrdinaryEmbedding.Controls
