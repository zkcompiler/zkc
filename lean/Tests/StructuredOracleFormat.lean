import ZkcTools.StructuredSource.WireTypes
import Zkc.Source.Structured.ContractElaboration
import Zkc.Source.Structured.ComponentExport
import Zkc.Source.Structured.Admission
import Zkc.Construction.Scalar
import Zkc.Construction.DomainTranscript
import Zkc.Construction.Projection
import Zkc.Construction.ConnectionOutputs

/-! Wire recognition is distinct from semantic admission. New logical sorts
must not inherit ordinary Math or message rights before the oracle profile. -/
set_option autoImplicit false
open Lean Zkc.Source.Structured ZkcTools.StructuredSource
namespace Tests.StructuredOracleFormat

private def run : IO Unit := do
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do throw (IO.userError name)
  let kind : OracleKind := .table (.field "koala-bear") (some 16)
  let unsized : OracleKind := .table (.field "koala-bear") none
  let maximum := indexLimit - 1
  for type in [Ty.oracle kind, .oracle unsized, .oracleSequence unsized maximum,
      .indices, .groups "bls12-381.g1"] do
    test "typed round trip" (Format.type (wireType type) == .ok type)
  test "field table data" (kind.data == .vector "koala-bear")
  test "index table data" ((OracleKind.table .index none).data == .indices)
  test "group table data" ((OracleKind.table (.group "g") none).data == .groups "g")
  test "query and answer" (kind.query == .index && kind.answer == .field "koala-bear")
  for value in ["-1", "01", "+1", "18446744073709551616"] do
    test "canonical capacity" (!(Format.type (.arr #[.str "oracle_sequence", wireOracleKind kind,
      .str value])).isOk)
  test "capacity requires string" (!(Format.type (.arr #[.str "oracle_sequence", wireOracleKind kind,
    toJson (4 : Nat)])).isOk)
  test "unknown kind" (!(Format.type (.arr #[.str "oracle", .arr #[.str "univariate", .arr #[]]])).isOk)
  test "nested handle is restricted" ((Ty.sequence (.oracle kind)).isHandle)
  test "oracle is not service" (!(Ty.oracle kind).isService)
  test "oracle type has no ordinary admission"
    (!(blsCatalogue.checkType blsCatalogue (.oracle kind)).isOk)
  test "nested handle has no ordinary admission"
    (!(blsCatalogue.checkType blsCatalogue (.sequence (.oracle kind))).isOk)
  for direction in [ContractDirection.input, .output] do
    let name := if direction == .input then "input" else "output"
    let selected : ContractSelector := ⟨direction, 0, "", true⟩
    test "anchor wire selector" (Format.contractSelector (.arr #[.str "anchor", .str name, toJson (0 : Nat)]) == .ok selected)
    test "anchor does not resolve as ordinary data" (!(selected.resolve
      ⟨"root", ["V"], [.vector "koala-bear"], [.vector "koala-bear"], [[0]], [[0]]⟩).isOk)
  for role in ["", "V"] do
    let signature : ProtocolSignature :=
      ⟨"root", ["V"], [.vector "koala-bear"], [], [[0]], []⟩
    test "typed selector cannot reinterpret anchor as participant data"
      ((ContractElaboration.selector? signature (.vector "koala-bear")
        ⟨.input, 0, role, true⟩).isNone)
  test "anchor extra role refused" (!(Format.contractSelector
    (.arr #[.str "anchor", .str "input", toJson (0 : Nat), .str "V"])).isOk)
  test "anchor noncanonical index refused" (!(Format.contractSelector
    (.arr #[.str "anchor", .str "input", .str "0"])).isOk)
  let bound := Json.arr #[.arr #[.str "rows", .str "32"]]
  test "kind owns named dimensions" (kind.shape == [("rows", some 16)])
  test "static shapes have no dynamic bounds" (Format.oracleShapeValues kind (.arr #[]) == .ok [])
  test "dynamic dimension bound retained" (Format.oracleShapeValues unsized bound == .ok [("rows", 32)])
  for malformed in [Json.null, .arr #[], .arr #[.arr #[.str "vars", .str "32"]],
      .arr #[.arr #[.str "rows", .str "32"], .arr #[.str "rows", .str "32"]],
      .arr #[.arr #[.str "rows", .str "18446744073709551616"]]] do
    test "malformed dynamic shape refused" (!(Format.oracleShapeValues unsized malformed).isOk)
  test "static dimension cannot acquire a dynamic bound" (!(Format.oracleShapeValues kind bound).isOk)
  test "send carries named dimensions" (Format.descriptor
    (.arr #[.str "oracle_send", .str "P", .arr #[.str "V"], wireOracleKind unsized,
      .arr #[.str "rows"], bound]) == .ok (.oracle (.send "P" ["V"] unsized ["rows"] [("rows",32)])))
  test "unnamed send shape refused" (!(Format.descriptor
    (.arr #[.str "oracle_send", .str "P", .arr #[.str "V"], wireOracleKind unsized, bound])).isOk)
  test "shape read names a kind dimension" (Format.descriptor
    (.arr #[.str "oracle_shape", wireOracleKind kind, .str "rows"]) == .ok (.oracle (.shape kind "rows")))
  test "shape read cannot invent a dimension" (!(Format.descriptor
    (.arr #[.str "oracle_shape", wireOracleKind kind, .str "vars"])).isOk)
  let descriptor := Json.arr #[.str "oracle_query", .null, wireOracleKind kind]
  test "query declaration owner omitted" (Format.descriptor descriptor == .ok (.oracle (.query none kind)))
  test "query role exact" (Format.descriptor (.arr #[.str "oracle_query", .str "V", wireOracleKind kind]) ==
    .ok (.oracle (.query (some "V") kind)))
  test "extra descriptor field refused" (!(Format.descriptor (.arr #[.str "oracle_query", .str "V",
    wireOracleKind kind, .null])).isOk)
  let deepest := (List.range 61).foldl (fun type _ => Ty.sequence type) (.oracle kind)
  test "kind and row consume the type depth budget" ((Format.type (wireType deepest)).isOk)
  test "nested kind cannot bypass the type depth budget"
    (!(Format.type (wireType (.sequence deepest))).isOk)
  test "logical handle cannot acquire scalar codec support"
    (!(Zkc.Construction.dataType (.oracle kind)) &&
     !(Zkc.Construction.dataType (.oracleSequence kind 4)))
  let anchor : OracleAnchor := ⟨⟨0, []⟩, .input 0⟩
  test "logical handle cannot become a transcript payload"
    ((Zkc.Construction.Domain.Payload.ofValue (carriers := uniformCarriers Nat Nat)
      (.oracle kind) anchor).isNone)
  test "aggregate cannot conceal a logical handle in a payload"
    ((Zkc.Construction.Domain.Payload.ofValue (carriers := uniformCarriers Nat Nat)
      (.sequence (.oracle kind)) [anchor]).isNone)
  test "logical handle cannot enter ordinary message projection"
    (!(Zkc.Construction.transportData (.oracle kind)))
  for type in [Ty.oracle kind, .oracleSequence kind 4, .sequence (.oracle kind)] do
    test "source connection refuses visible logical-handle outputs"
      ((Zkc.Construction.Original.roleOutputSorts 0 [[0]] [type]).isNone)
    test "source connection retains absent logical-handle outputs"
      (Zkc.Construction.Original.roleOutputSorts 0 [[1]] [type] == some [])
  IO.println s!"structured-oracle-format: {← count.get} controls passed"

#eval run
end Tests.StructuredOracleFormat
