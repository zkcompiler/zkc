import Zkc.Source.Structured.Import
import Zkc.Source.Structured.ComponentRoutes
import ZkcTools.StructuredSource.OpenEvaluation

/-! The wire reader recognizes logical oracle syntax without granting ordinary
execution, component routes, or aggregate payload rights. -/
set_option autoImplicit false
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredOracleAdmission

private def kind : OracleKind := .table (.field "koala-bear") (some 16)

private def instruction : Instruction :=
  .instruction (.oracle (.sequenceLength kind 4)) [] [.index] [] "logical"

private def owner : Function :=
  ⟨"main", .protocol, .publicDef, [], [.index],
    some ⟨["P", "V"], [], [["P", "V"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [instruction] (.ret [0])⟩

private def snapshot : Snapshot :=
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000", "main",
    [], [], [], [.function owner], [⟨"main", []⟩], blsRows, {}⟩

private def run : IO Unit := do
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do throw (IO.userError name)
  test "oracle descriptor decodes independently"
    ((Format.descriptor (.arr #[.str "oracle_sequence_length",
      ZkcTools.StructuredSource.wireOracleKind kind, .str "4"])).isOk)
  test "ordinary protocol refuses decoded logical operation" (!(check snapshot).isOk)
  test "realization preparation refuses nested logical handles"
    (!(PreparationProfile.realization.typeAllowed (.sequence (.oracle kind))))
  test "ordinary availability refuses empty aggregate handle types"
    (!(Availability.noHandles [.sequence (.oracle kind)] |>.run {}).isOk)
  test "ordinary math selection refuses logical handles"
    (!(resolveOp snapshot [] .math [] [] [] (.select (.oracle kind)) []
      [.oracle kind] "" |>.run {}).isOk)
  test "component analysis refuses logical operation"
    (match (ComponentRoutes.block snapshot owner 64 owner.body [] [] [] [] []).run {} with
     | .error message => message == "component-seam-oracle"
     | .ok _ => false)
  let dormant := {snapshot with definitions := [.function {owner with
    body := .block [] (.ret []), outputs := [],
    interface := some ⟨["P", "V"], [], []⟩},
    .oracle ⟨"unused", [], kind, "admissible", [], [], .block [] (.ret [])⟩]}
  test "dormant oracle declaration grants no ordinary execution" (!(check dormant).isOk)
  let input := ZkcTools.StructuredSource.input
  let zero : Json := .str "0"
  test "group data collection exact domain"
    ((input (.groups "g") (.arr #[.str "groups", .str "g", .arr #[zero]])).isOk)
  test "group data collection wrong domain"
    (!(input (.groups "g") (.arr #[.str "groups", .str "other", .arr #[zero]])).isOk)
  test "field data collection wrong domain"
    (!(input (.vector "f") (.arr #[.str "vector", .str "other", .arr #[zero]])).isOk)
  test "data collection extra field refused"
    (!(input (.groups "g") (.arr #[.str "groups", .str "g", .arr #[], .null])).isOk)
  test "index data collection admitted"
    ((input .indices (.arr #[.str "indices", .arr #[toJson (0 : Nat)]])).isOk)
  test "index data collection rejects decimal strings"
    (!(input .indices (.arr #[.str "indices", .arr #[zero]])).isOk)
  test "sequence exact element domain"
    (!(input (.sequence (.groups "g")) (.arr #[.str "sequence",
      ZkcTools.StructuredSource.wireType (.groups "other"), .arr #[]])).isOk)
  for ty in [Ty.oracle kind, .oracleSequence kind 4] do
    test "logical value cannot enter ordinary external input" (!(input ty .null).isOk)
  test "empty sequence cannot hide a logical element type"
    (!(input (.sequence (.oracle kind)) (.arr #[.str "sequence",
      ZkcTools.StructuredSource.wireType (.oracle kind), .arr #[]])).isOk)
  test "empty logical sequence has no ordinary output encoding"
    (!(ZkcTools.StructuredSource.output (.sequence (.oracle kind)) []).isOk)
  let nested := Ty.product "T" "mk" (.cons (.sequence (.oracle kind)) .nil)
  test "open input rejects empty logical aggregates"
    (!(ZkcTools.StructuredSource.wireInput (.sequence (.oracle kind)) (.arr #[])).isOk)
  test "open input rejects nested empty logical aggregates"
    (!(ZkcTools.StructuredSource.wireInput nested (.arr #[.arr #[]])).isOk)
  test "open output rejects empty logical aggregates"
    (!(ZkcTools.StructuredSource.wireOutput (.sequence (.oracle kind)) []).isOk)
  test "open output rejects nested empty logical aggregates"
    (!(ZkcTools.StructuredSource.wireOutput nested ([], ())).isOk)
  test "open output rejects bounded logical sequences"
    (!(ZkcTools.StructuredSource.wireOutput (.oracleSequence kind 0) []).isOk)
  test "open input rejects absent logical ports"
    (!(ZkcTools.StructuredSource.optionalInputs [.oracle kind] [.null]).isOk)
  test "open output rejects absent logical ports"
    (!(ZkcTools.StructuredSource.optionalOutputs
      (Values.cons (ty := .oracle kind) none .nil)).isOk)
  test "open receive request rejects logical message schemas"
    (!(ZkcTools.StructuredSource.actionRequest ["P", "V"] 0
      (.receive (.sequence (.oracle kind)) "logical" 1)).isOk)
  test "product identity exact"
    (!(input (.product "T" "mk" .nil)
      (.arr #[.str "product", .str "Other", .str "mk", .arr #[]])).isOk)
  IO.println s!"structured-oracle-admission: {← count.get} controls passed"

#eval run
end Tests.StructuredOracleAdmission
