import ZkcTools.StructuredSource.WireTypes
import Zkc.Source.Structured.Admission
import Zkc.Construction.Scalar
import Zkc.Construction.DomainTranscript
import Zkc.Construction.Projection

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
  IO.println s!"structured-oracle-format: {← count.get} controls passed"

#eval run
end Tests.StructuredOracleFormat
