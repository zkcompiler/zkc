import Zkc.Source.Structured.OracleObligations

set_option autoImplicit false
open Lean Zkc.Source.Structured
namespace Tests.StructuredOracleObligations
open OracleObligations

private def kind : OracleKind := .table (.field "koala-bear") (some 16)
private def body : Block := .block [
  .instruction (.oracle (.query none kind)) [0, 1] [.field "koala-bear"] [] "first",
  .instruction (.oracle (.query none kind)) [1, 2] [.field "koala-bear"] [] "second"] (.ret [0])
private def snapshot : Snapshot := {
  source := String.ofList (List.replicate 64 'a'), entry := "root",
  domains := [], relations := [], bindings := [], catalogue := ⟨[], [], []⟩,
  definitions := [.oracle ⟨"twice", [.oracle kind, .index], kind, "admissible", [], [], body⟩] }

private def run : IO Unit := do
  let count ← IO.mkRef 0
  let failures ← IO.mkRef ([] : List String)
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let expected : Report := ⟨snapshot.source, "root",
    [⟨.queryDomain, [7, 0, 7, 1, 0]⟩, ⟨.queryDomain, [7, 0, 7, 1, 1]⟩],
    [⟨0, 1, [⟨[7, 0, 7, 1, 0], 0, 1⟩, ⟨[7, 0, 7, 1, 1], 0, 2⟩]⟩]⟩
  let result ← IO.ofExcept (derive snapshot)
  test "repeated queries retain distinct actual rows" (result == expected)
  test "independent complete report accepted" ((check snapshot (wire expected)).isOk)
  for changed in [
      {expected with source := "different"},
      {expected with entry := "different"},
      {expected with conditions := expected.conditions.reverse},
      {expected with conditions := expected.conditions.drop 1},
      {expected with conditions := expected.conditions ++ expected.conditions},
      {expected with footprints := []},
      {expected with footprints := [⟨0, 1, [⟨[7,0,7,1,0],0,1⟩]⟩]},
      {expected with footprints := [⟨0, 1, [⟨[7,0,7,1,0],0,1⟩, ⟨[7,0,7,1,1],0,1⟩]⟩]},
      {expected with footprints := [⟨0, 2, [⟨[7,0,7,1,0],0,1⟩, ⟨[7,0,7,1,1],0,2⟩]⟩]}] do
    test "changed source condition or footprint refused" (!(check snapshot (wire changed)).isOk)
  let malformed := Json.arr #[.str "zkc.oracle-obligations/0", .str snapshot.source,
    .str snapshot.entry, toJson ([] : List Json), toJson ([] : List Json), .null]
  test "unknown slot refused" (!(decode malformed).isOk)
  test "objects refused" (!(decode (Json.mkObj [])).isOk)
  let invalidBody := Block.block [
    .instruction (.oracle (.query none kind)) [0,1] [.field "koala-bear"] [] "first",
    .instruction (.oracle (.query none kind)) [0,2] [.field "koala-bear"] [] "wrong_source"] (.ret [0])
  let invalid := {snapshot with definitions := [.oracle
    ⟨"twice", [.oracle kind, .index], kind, "admissible", [], [], invalidBody⟩]}
  test "query source must be an actual declared handle" (!(derive invalid).isOk)
  let failed ← failures.get
  IO.println s!"structured-oracle-obligations: {← count.get} controls, {failed.length} failures"
  unless failed.isEmpty do throw (IO.userError (String.intercalate "\n" failed.reverse))

#eval run
end Tests.StructuredOracleObligations
