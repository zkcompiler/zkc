import ZkcTools.StructuredSource.WireTypes
import Zkc.Source.Structured.ContractElaboration
import Zkc.Source.Structured.ComponentExport
import Zkc.Source.Structured.Admission
import Zkc.Construction.Scalar
import Zkc.Construction.DomainTranscript
import Zkc.Construction.Structured
import Zkc.Construction.ConnectionOutputs
import Zkc.Construction.ConnectionRootInputs
import Zkc.Construction.ConnectionRepeatSupport

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
    test "canonical capacity" (!(Format.type (.arr #[.str "oracle_sequence", .str "table", wireOracleArguments (.field "koala-bear") (some 16),
      .str value])).isOk)
  test "capacity requires string" (!(Format.type (.arr #[.str "oracle_sequence", .str "table", wireOracleArguments (.field "koala-bear") (some 16),
    toJson (4 : Nat)])).isOk)
  test "unknown kind" (!(Format.type (.arr #[.str "oracle", .str "univariate", .arr #[]])).isOk)
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
  let virtualRow := Json.arr #[.str "oracle", .str "dynamic",
    .arr #[wireType (.oracle unsized), wireType .index, wireType .index], wireOracleKind unsized,
    .str "admissible", .arr #[.arr #[.str "rows", .str "1"]], bound,
    .arr #[.str "block", .arr #[], .arr #[.str "return", .arr #[]]]]
  test "dynamic declaration retains named argument and bound"
    (match Format.definition virtualRow with
     | .ok (.oracle declaration) => declaration.shapeArguments == [("rows", 1)] &&
         declaration.shapeBounds == [("rows", 32)] && declaration.kind == unsized
     | _ => false)
  if let .arr fields := virtualRow then
    test "declaration unknown field refused" (!(Format.definition (.arr (fields.push .null))).isOk)
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
  let k := wireOracleKind kind
  let names := Json.arr #[.str "rows"]
  let receivers := Json.arr #[.str "V"]
  let empty := Json.arr #[]
  let singleton := wireType (.oracle kind)
  let descriptors : List (Json × OracleDescriptor) := [
    (.arr #[.str "oracle_input", .str "P", receivers, singleton, empty],
      .input "P" ["V"] (.oracle kind) []),
    (.arr #[.str "oracle_send", .str "P", receivers, k, names, empty],
      .send "P" ["V"] kind ["rows"] []),
    (.arr #[.str "oracle_query", .str "V", k], .query (some "V") kind),
    (.arr #[.str "oracle_contents", .str "P", k], .contents "P" kind),
    (.arr #[.str "oracle_components", .str "P", receivers, singleton],
      .components "P" ["V"] (.oracle kind)),
    (.arr #[.str "oracle_shape", k, .str "rows"], .shape kind "rows"),
    (.arr #[.str "oracle_forget_shape", k, wireOracleKind unsized], .forgetShape kind unsized),
    (.arr #[.str "oracle_virtual", .str "map", .str "P", receivers, k],
      .virtual "map" "P" ["V"] kind),
    (.arr #[.str "oracle_sequence_empty", k, .str "4"], .sequenceEmpty kind 4),
    (.arr #[.str "oracle_sequence_append", k, .str "4", receivers], .sequenceAppend kind 4 ["V"]),
    (.arr #[.str "oracle_sequence_at", k, .str "4", receivers], .sequenceAt kind 4 ["V"]),
    (.arr #[.str "oracle_sequence_length", k, .str "4"], .sequenceLength kind 4)]
  for (json, expected) in descriptors do
    test "all twelve exact descriptor cases" (Format.descriptor json == .ok (.oracle expected))
    if let .arr fields := json then
      test "all twelve reject unknown fields" (!(Format.descriptor (.arr (fields.push .null))).isOk)
  for capacity in [0, 4, maximum] do
    let sort := Ty.oracleSequence unsized capacity
    test "input retains sequence capacity independently of row bound" (Format.descriptor
      (.arr #[.str "oracle_input", .str "P", receivers, wireType sort, bound]) ==
        .ok (.oracle (.input "P" ["V"] sort [("rows", 32)])))
    test "components retain sequence capacity" (Format.descriptor
      (.arr #[.str "oracle_components", .str "P", receivers, wireType sort]) ==
        .ok (.oracle (.components "P" ["V"] sort)))
  for sort in [k, wireType .index, wireType (.sequence (.oracle kind)),
      .arr #[.str "oracle_sequence", .str "table",
        wireOracleArguments (.field "koala-bear") none, .str "18446744073709551616"]] do
    test "input refuses obsolete kinds and nonlogical sorts" (!(Format.descriptor
      (.arr #[.str "oracle_input", .str "P", receivers, sort, empty])).isOk)
    test "components refuse obsolete kinds and nonlogical sorts" (!(Format.descriptor
      (.arr #[.str "oracle_components", .str "P", receivers, sort])).isOk)
  let deepest := (List.range 19).foldl (fun type _ => Ty.sequence type) (.oracle kind)
  test "kind and row fit the expanded depth budget" ((Format.type (wireType deepest)).isOk)
  test "nested kind cannot bypass the expanded depth budget"
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
    ((Zkc.Construction.dataSort? (.oracle kind)).isNone)
  let hidden : Ty := .product "tuple" "value"
    (.cons (.sequence (.oracleSequence kind 4)) (.cons .boolean .nil))
  test "nested tuple sequence handles are excluded" hidden.isHandle
  test "tuple admission cannot conceal handles" (!(blsCatalogue.checkType blsCatalogue hidden).isOk)
  test "tuple payload cannot conceal handles"
    ((Zkc.Construction.Domain.Payload.ofValue (carriers := uniformCarriers Nat Nat)
      hidden ([[anchor]], (true, ()))).isNone)
  test "empty tuple sequence still excludes its handle element type"
    ((Zkc.Construction.Domain.Payload.ofValue (carriers := uniformCarriers Nat Nat)
      hidden ([], (true, ()))).isNone)
  for type in [Ty.oracle kind, .oracleSequence kind 4, .sequence (.oracle kind), hidden] do
    test "source connection refuses visible logical-handle outputs"
      ((Zkc.Construction.Original.roleOutputSorts 0 [[0]] [type]).isNone)
    test "source connection retains absent logical-handle outputs"
      (Zkc.Construction.Original.roleOutputSorts 0 [[1]] [type] == some [])
    test "source connection refuses visible logical-handle inputs"
      (match Zkc.Construction.ConnectionRootInputs.inputLocations 0 [] [type] [[0]] 0 0 with
       | .error message => message == "connection-input-not-data"
       | .ok _ => false)
    test "source connection retains absent logical-handle inputs"
      ((Zkc.Construction.ConnectionRootInputs.inputLocations 0 [] [type] [[1]] 0 0).isOk)
    test "native loop state excludes logical handles"
      (!(Zkc.Construction.ConnectionFrame.visibleState 0 [[0]] [type]))
  test "native loop state retains ordinary oracle Data"
    (Zkc.Construction.ConnectionFrame.visibleState 0 [[0]] [kind.data])
  IO.println s!"structured-oracle-format: {← count.get} controls passed"

#eval run
end Tests.StructuredOracleFormat
