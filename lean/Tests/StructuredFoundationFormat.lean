import Zkc.Source.Structured.Format

/-! Authored synthetic fixtures for the landed structured source schema.
These are decoder controls, not native captures or correspondence evidence. -/

open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredFoundationFormat

private def arr (values : List Json) : Json := .arr values.toArray
private def strs (values : List String) : Json := arr (values.map Json.str)
private def app (name : String) (args : List Json := []) : Json :=
  arr [.str "apply", .str name, arr args]
private def root (sort name : String) : Json := strs ["domain", sort, name]
private def field (name : String := "f") : Json := app "field" [root "Field" name]
private def vector (name : String := "f") : Json := app "vector" [root "Field" name]
private def atom (value : String) : Json := strs ["atom", value]
private def tuple (values : List Json) : Json := arr [.str "tuple", arr values]
private def product (identity : Json) (fields : List Json := []) : Json :=
  arr [.str "variant", identity, arr [arr [.str "make", arr fields]]]
private def binding (contract : String) (args inputs outputs : List Json)
    (implementation : String := "") : Json :=
  arr [.str "binding", .str "primitive", .str contract, arr args,
    .str implementation, arr inputs, arr outputs]
private def refused {α : Type} (value : Except String α) (code : String) : Bool :=
  match value with | .error actual => actual == code | _ => false

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  for (name, wire, expected) in [
      ("bool", app "bool", Ty.boolean), ("index", app "index", Ty.index),
      ("indices", app "indices", Ty.indices), ("field", field, Ty.field "f"),
      ("vector", vector, Ty.vector "f"),
      ("group", app "group" [root "Group" "g"], Ty.group "g"),
      ("groups", app "groups" [root "Group" "g"], Ty.groups "g"),
      ("sequence", app "sequence" [arr [.str "type", field]], Ty.sequence (.field "f")),
      ("service", strs ["service", "random.f/0"], Ty.service "random.f/0")] do
    test ("type:" ++ name) (match Format.type wire with | .ok actual => actual == expected | _ => false)
  for old in [strs ["bool"], strs ["index"], strs ["indices"], strs ["field", "f"],
      strs ["group", "g"], arr [.str "sequence", field],
      arr [.str "product", .str "[\"R\"]", .str "make", arr []],
      .str "!algebra.field<f>", .str "variant:deadbeef"] do
    test "retired-type-wire" (!(Format.type old).isOk)
  for bad in [app "unknown", app "bool" [root "Field" "f"], app "field",
      app "field" [root "Group" "f"], app "field" [strs ["nat", "1"]],
      app "field" [.str "f"], app "sequence" [root "Field" "f"],
      app "fixed_vector" [arr [.str "type", field], strs ["nat", "01"]],
      app "fixed_vector" [arr [.str "type", field], strs ["nat", "18446744073709551616"]],
      app "resource_unit" [root "Slot" "1bad"],
      app "resource_unit" [root "Slot" "bad/name"]] do
    test "complete-type-shape-refusal" (!(LogicalFormat.type bad).isOk)
  let fixed := app "fixed_vector" [arr [.str "type", field], strs ["nat", "5"]]
  test "data-vocabulary-fixed-array" ((LogicalFormat.type fixed).isOk)
  test "fixed-array-profile-refusal" (refused (Format.type fixed) "structured-type-unsupported")
  let sum := arr [.str "variant", atom "Choice", arr [
    arr [.str "left", arr [field]], arr [.str "right", arr []]]]
  test "data-vocabulary-sum" ((LogicalFormat.type sum).isOk)
  test "sum-profile-refusal" (refused (Format.type sum) "structured-type-unsupported")
  for bad in [arr [.str "variant", atom "R", arr []],
      arr [.str "variant", atom "R", arr [arr [.str "same", arr []], arr [.str "same", arr [field]]]],
      arr [.str "variant", atom "R", arr [arr [.str "bad/name", arr []]]],
      product (.str "R"), product (strs ["atom", ""]),
      product (arr [.str "tuple", arr [Json.num 0]])] do
    test "nominal-shape-refusal" (!(LogicalFormat.type bad).isOk)
  test "alternative-label-limit" (!(LogicalFormat.type (arr [.str "variant", atom "R",
    arr [arr [.str (String.ofList (List.replicate 129 'a')), arr []]]])).isOk)
  test "alternative-count-limit" (!(LogicalFormat.type (arr [.str "variant", atom "R",
    arr ((List.range 513).map fun i => arr [.str ("case" ++ toString i), arr []])])).isOk)
  test "payload-count-limit" (!(LogicalFormat.type
    (product (atom "R") (List.replicate 513 (app "bool")))).isOk)
  let phantomA := product (tuple [atom "Record", atom "A"]) [field, app "bool"]
  let phantomB := product (tuple [atom "Record", atom "B"]) [field, app "bool"]
  test "phantom-static-identity" (match Format.type phantomA, Format.type phantomB with
    | .ok left, .ok right => left != right | _, _ => false)
  test "payload-order" (match Format.type phantomA,
      Format.type (product (tuple [atom "Record", atom "A"]) [app "bool", field]) with
    | .ok left, .ok right => left != right | _, _ => false)
  test "identity-atom-versus-tuple" (match Format.type (product (atom "R")),
      Format.type (product (tuple [atom "R"])) with
    | .ok left, .ok right => left != right | _, _ => false)
  test "canonical-unicode-and-controls" (match LogicalFormat.identity (atom "é\t\x08\x0c\n\"\\") with
    | .ok actual => actual == "\"é\\t\\b\\f\\n\\\"\\\\\"" | _ => false)
  test "unicode-not-normalized" (match LogicalFormat.identity (atom "é"),
      LogicalFormat.identity (atom "é") with
    | .ok left, .ok right => left != right | _, _ => false)
  test "empty-product" (match Format.type (product (tuple [])) with
    | .ok (.product "[]" "make" .nil) => true | _ => false)
  test "identity-profile-bound" (refused
    (Format.type (product (atom (String.ofList (List.replicate 511 'a'))))) "structured-string")
  let oracleArgs := arr [arr [.str "type", field], strs ["nat", "4"]]
  test "oracle-complete-row" (match Format.type (arr [.str "oracle", .str "table", oracleArgs]) with
    | .ok (.oracle (.table (.field "f") (some 4))) => true | _ => false)
  test "oracle-sequence" (match Format.type (arr [
      .str "oracle_sequence", .str "table", oracleArgs, .str "8"]) with
    | .ok (.oracleSequence (.table (.field "f") (some 4)) 8) => true | _ => false)
  test "retired-oracle-type" (!(Format.type (arr [
    .str "oracle", arr [.str "table", oracleArgs]])).isOk)
  for bad in [arr [.str "oracle", .str "missing", oracleArgs],
      arr [.str "oracle", .str "table", arr [root "Field" "f"]],
      arr [.str "oracle_sequence", .str "table", oracleArgs, .str "-1"]] do
    test "oracle-kind-refusal" (!(LogicalFormat.type bad).isOk)
  let signatures := [
    ("index.constant", [], [], [app "index"]),
    ("index.add", [], [app "index", app "index"], [app "index"]),
    ("index.sub", [], [app "index", app "index"], [app "index"]),
    ("index.mul", [], [app "index", app "index"], [app "index"]),
    ("index.div", [], [app "index", app "index"], [app "index"]),
    ("index.mod", [], [app "index", app "index"], [app "index"]),
    ("index.equal", [], [app "index", app "index"], [app "bool"]),
    ("index.less", [], [app "index", app "index"], [app "bool"]),
    ("vector.empty", [root "Field" "f"], [], [vector]),
    ("vector.length", [root "Field" "f"], [vector], [app "index"]),
    ("vector.sum", [root "Field" "f"], [vector], [field]),
    ("vector.split", [root "Field" "f"], [vector], [vector, vector]),
    ("vector.append", [root "Field" "f"], [vector, field], [vector]),
    ("vector.equal", [root "Field" "f"], [vector, vector], [app "bool"]),
    ("field.equal", [root "Field" "f"], [field, field], [app "bool"])]
  for (contract, args, inputs, outputs) in signatures do
    test (contract ++ ":binding") ((Format.binding (binding contract args inputs outputs)).isOk)
    test (contract ++ ":complete-signature") (refused
      (Format.binding (binding contract args inputs (outputs ++ [app "bool"])))
      "structured-binding-signature")
    test (contract ++ ":unselected") (!(Format.binding
      (binding contract args inputs outputs "native")).isOk)
  for args in [[.str "f"], [root "Group" "f"], [strs ["nat", "1"]],
      [arr [.str "type", field]], [arr [.str "mask", arr [Json.bool true]]],
      [root "Field" "f", root "Field" "f"]] do
    test "kinded-root-refusal" (!(Format.binding
      (binding "field.equal" args [field, field] [app "bool"])).isOk)
  test "ordered-signature-refusal" (refused (Format.binding
    (binding "vector.append" [root "Field" "f"] [field, vector] [vector]))
    "structured-binding-signature")
  test "nominal-signature-refusal" (refused (Format.binding
    (binding "field.equal" [root "Field" "f"] [field, field "other"] [app "bool"]))
    "structured-binding-signature")
  test "retired-five-field-binding" (!(Format.binding (arr [
    .str "binding", .str "primitive", .str "index.add", arr [], .str ""])).isOk)
  test "unknown-contract-cannot-enroll" (!(Format.binding
    (binding "field.unknown" [root "Field" "f"] [field, field] [app "bool"])).isOk)
  for (wire, expected) in [(arr [], []),
      (arr [strs ["natural", "0"]], ["0"]),
      (arr [strs ["natural", "18446744073709551615"]], ["18446744073709551615"])] do
    test "structured-natural" (match Format.primitiveParameters wire with
      | .ok actual => actual == expected | _ => false)
  for bad in [strs ["0"], arr [strs ["natural", "01"]],
      arr [strs ["natural", "18446744073709551616"]], arr [strs ["natural", "-1"]],
      arr [arr [.str "natural", Json.num 0]],
      arr [strs ["field_literal", "f", "natural", "0"]],
      arr [arr [.str "expression", arr []]]] do
    test "parameter-refusal" (!(Format.primitiveParameters bad).isOk)
  test "exec-structured-parameters" (match Format.descriptor (arr [
      .str "exec", .str "exec.apply", .str "primitive", arr [strs ["natural", "7"]]]) with
    | .ok (.exec "exec.apply" "primitive" ["7"]) => true | _ => false)
  let digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
  let origin := arr [.str "Library::specialize", arr [arr [.str "F", strs ["field", "f"]]]]
  let definition := arr [.str "function", .str "main", .str "protocol", .str "public",
    arr [field], arr [field], arr [.str "protocol", strs ["P"], arr [strs ["P"]], arr [strs ["P"]]],
    arr [], origin, arr [.str "block", arr [], arr [.str "return", arr [Json.num 0]]]]
  let declarations := arr [arr [], arr []]
  let envelope := [.str "zkc.structured-source/0", .str "original", .str digest,
    .str "main", arr [], arr [], arr [], arr [definition], arr [], arr [arr [], arr []], declarations]
  test "origin-source-association" (match Format.snapshot (arr envelope) with
    | .ok value => value.source == digest && value.entry == "main" &&
      (match value.definitions with
        | [.function function] => function.inputs == [.field "f"] &&
          function.outputs == [.field "f"] && function.origin ==
          some (.protocol ⟨"Library::specialize", [("F", .field "f")]⟩)
        | _ => false)
    | _ => false)
  test "unused-forged-binding" (refused (Format.snapshot (arr (envelope.set 6
    (arr [binding "index.add" [] [app "index", app "index"] [app "bool"]]))))
    "structured-binding-signature")
  let withBinding := envelope.set 6 (arr [binding "index.add" []
    [app "index", app "index"] [app "index"]])
  test "snapshot-retains-binding-schema" (match Format.snapshot (arr withBinding) with
    | .ok value => match value.bindings with
      | [binding] => value.source == digest && binding.schema ==
          some ⟨[], [.index, .index], [.index]⟩
      | _ => false
    | _ => false)
  let rows := arr [arr [
    arr [.str "nominal", .str "base", .str "Field", arr [], strs ["Field"], .str "5"],
    arr [.str "nominal", .str "extension", .str "Field", arr [strs ["BaseField", "base"]],
      strs ["Field", "ExtensionField"], .str "5"]], arr []]
  let withEmbedding := (envelope.set 9 rows).set 6 (arr [binding "field.embed"
    [root "Field" "extension"] [field "base"] [field "extension"]])
  test "snapshot-unused-embedding" ((Format.snapshot (arr withEmbedding)).isOk)
  test "snapshot-unused-forged-embedding" (refused (Format.snapshot (arr (withEmbedding.set 6
    (arr [binding "field.embed" [root "Field" "extension"] [field "other"] [field "extension"]]))))
    "structured-binding-signature")
  test "source-parser-current-schema" ((Format.parse (arr envelope).compress >>= Format.snapshot).isOk)
  test "source-parser-object-refusal" (refused (Format.parse "{}") "invalid-shape")
  for bad in ["\"\\ud800\"", "\"\\udfff\"", "\"\\ud800x\"", "\"\\ud800\\u1234\""] do
    test "unicode-surrogate-refusal" (refused (Format.parse bad) "logical-unicode")
  test "unicode-surrogate-pair" (match Format.parse "\"\\ud83d\\ude00\"" with
    | .ok (.str "😀") => true | _ => false)
  test "unicode-escaped-backslash" (match Format.parse "\"\\\\ud800\"" with
    | .ok (.str "\\ud800") => true | _ => false)
  test "logical-expanded-work" (!LogicalFormat.workWithin 2 67108864 [(1, product (atom "R"))])
  test "logical-metadata-budget" (!LogicalFormat.workWithin 100 1 [(1, atom "R")])
  let deep := (List.range 65).foldl (fun value _ => tuple [value]) (atom "R")
  test "logical-depth" (!(LogicalFormat.identity deep).isOk)
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError (String.intercalate "\n" errors.reverse))
  IO.println s!"Structured foundation format: {← count.get} controls passed"

#eval run

end Tests.StructuredFoundationFormat
