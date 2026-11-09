import Zkc.Tests.IR.OracleProcessData

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
open Tests.OracleProcessData
namespace Tests.OracleProcessSource

private def root : Definition := .function
  ⟨"main", .protocol, .publicDef, [.indices, .oracle kind], [.index],
    some ⟨["P", "V"], [["P"], ["V"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [
      .instruction (.oracle (.input "P" ["V"] (.oracle kind) [])) [0, 1] [.oracle kind] [] "",
      .instruction (.oracle (.virtual "Repeated" "P" ["V"] kind)) [0] [.oracle kind] [] "",
      .instruction (.oracle (.virtual "Repeated" "P" ["V"] kind)) [0] [.oracle kind] [] "",
      .instruction (.indexConstant "0") [] [.index] [] "",
      .instruction (.oracle (.query (some "V") kind)) [1, 0] [.index] [] "read"] (.ret [0])⟩

private def source : Snapshot :=
  {snapshot with
    definitions := [.function predicate, .oracle declaration, root]
    contracts := [⟨"main", []⟩]
    relations := [⟨"admissible_rows", .privateDef, "zkc.language.formula/0", "rows", "0",
      [.indices], [.boolean], ["parameter"], some "admissible", []⟩]}

private def test (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError name)

private def replace {V : Ty → Type} {types : List Ty} {type : Ty} :
    Values V types → Var types type → V type → Values V types
  | .cons _ rest, .here, value => .cons value rest
  | .cons head rest, .there position, value => .cons head (replace rest position value)

private def controls : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let test (name : String) (condition : Bool) : IO Unit := do
    test name condition
    count.modify (· + 1)
  let imported : Imported source ← match admitted : check source with
    | .error code => throw (IO.userError ("source admission: " ++ code))
    | .ok program => pure ⟨program, admitted⟩
  let subject ← match imported.oracleSubject with
    | .error code => throw (IO.userError code)
    | .ok subject => pure subject
  let root := subject.unit.snapshot.definitions.findIdx (·.name == subject.unit.snapshot.entry)
  let inputAnchor : OracleAnchor := ⟨⟨root, []⟩, .input 1⟩
  let types := subject.imported.program.payload.entry.inputs
  let some dataPort := Var.decode types .indices 0 | throw (IO.userError "data port")
  let some handlePort := Var.decode types (.oracle kind) 1 | throw (IO.userError "handle port")
  for self in [0, 1] do
    let inputs := replace (replace (Values.absent model.Value types) dataPort
      (if self == 0 then some [10, 20] else none)) handlePort
      (if self == 1 then some inputAnchor else none)
    let start ← match subject.start model self inputs [2] ({} : Provider) with
      | .error code => throw (IO.userError ("root ingress: " ++ code))
      | .ok start => pure start
    have associated := subject.source
    have represented := OracleProcess.source_represents start (ordinary false) (base none)
    have exactIdentity := OracleProcess.sourceRunM_pure (m := Id) start (ordinary false) (base none)
    let _ := associated
    let _ := represented
    let _ := exactIdentity
    let result := OracleProcess.sourceRunM (m := Id) start (ordinary false) (base none)
    have reachable : OracleProtocol.Reachable result.state :=
      OracleProcess.sourceRunM_reachable start (ordinary false) (base none)
    let _ := reachable
    test "root returns through actual source protocol" (match result.outcome with
      | .returned _ => true | _ => false)
    test "complete source event log"
      (result.events == (start.run (ordinary false) (base none)).events)
    test "source result agrees with its typed selected output" (match result.outcome with
      | .stopped _ => false
      | .returned values => match Var.decode _ .index 0 with
        | none => false
        | some output => (values.get output).bind ProtocolValue.toConcrete ==
            (if self == 1 then some 10 else none))
    test "root retains input base plus two virtual tables" (result.state.oracle.entries.length == 3)
    if self == 1 then
      test "receiver expands nested source-backed virtual definitions"
        (result.state.oracle.queries == 7 && result.state.oracle.provider.calls == 4 &&
          result.state.oracle.provider.hits == 3)
      test "receiver base query uses actual root input anchor"
        (result.state.oracle.provider.cache == [(inputAnchor, 0)])
      let failed := OracleProcess.sourceRunM (m := Id) start
        (ordinary false) (base (some (2, .abort)))
      test "failed source root retains child post-state and log" (match failed.outcome with
        | .stopped .abort => failed.state.oracle.provider.calls == 2 &&
            failed.state.oracle.provider.hits == 1 && failed.state.oracle.queries == 4
        | _ => false)
    else
      test "holder skips role-invisible queries"
        (result.state.oracle.queries == 0 && result.state.oracle.provider.calls == 0)
  IO.println s!"oracle-process-source: {← count.get} controls passed"

#eval controls

end Tests.OracleProcessSource
