import Tests.StructuredOriginFixture
import ZkcTools.StructuredSource.Root
import Zkc.Source.Structured.ModelAdmission

/-! Strict origin controls, including direct raw-record admission. Authored
fixtures do not establish native export or body correspondence. -/
set_option autoImplicit false
open Lean Zkc.Source.Structured ZkcTools.StructuredSource.Root
open Tests.StructuredOriginFixture

namespace Tests.StructuredOrigin

private def nested : Nat → OriginTerm
  | 0 => .unit
  | n + 1 => .array (nested n) "1"

private def repeated (n : Nat) (c : Char := 'a') : String := String.ofList (List.replicate n c)

private def rawSnapshot (function : Function) : Snapshot :=
  { snapshot with
    definitions := [.function function], contracts := [⟨function.name, []⟩],
    entry := function.name }

private def headerRefused (origin : Option FunctionOrigin) (mode : Kind := .protocol) : Bool :=
  let function := { leaf with
    name := "main", kind := mode,
    visibility := if mode == .protocol then .publicDef else .privateDef,
    interface := if mode == .protocol then leaf.interface else none, origin := origin }
  let input := rawSnapshot function
  !(checkUnitHeaders input).isOk && !(check input).isOk && !(checkFormedPayload input).isOk

private def refusedWith {α : Type} (code : String) : Except String α → Bool
  | .error actual => actual == code
  | .ok _ => false

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  test "structured-origin-array" (refusedWith "structured-origin-array" (OriginFormat.protocol .null))
  test "structured-origin-list-limit" (refusedWith "structured-origin-list-limit"
    (OriginFormat.protocol (toJson [toJson "P", toJson ([] : List Json), toJson "extra"])))
  test "structured-origin-string" (refusedWith "structured-origin-string"
    (OriginFormat.term 64 (toJson ["field", ""])))
  test "structured-origin-decimal" (refusedWith "structured-origin-decimal"
    (OriginFormat.term 64 (toJson ["nat", "01"])))
  test "structured-origin-nominal-kind" (refusedWith "structured-origin-nominal-kind"
    (OriginFormat.term 64 (toJson [toJson "nominal", toJson "unknown", toJson "T", toJson ([] : List Json)])))
  test "structured-origin-path" (refusedWith "structured-origin-path"
    (OriginFormat.term 64 (toJson [toJson "nominal", toJson "record", toJson "a/b", toJson ([] : List Json)])))
  test "structured-origin-depth" (refusedWith "structured-origin-depth" (OriginFormat.term 0 (toJson ["unit"])))
  test "structured-origin-term" (refusedWith "structured-origin-term" (OriginFormat.term 64 (toJson ["unknown"])))
  test "structured-origin" (refusedWith "structured-origin" (OriginFormat.protocol (toJson ([] : List Json))))
  test "structured-origin-binding" (refusedWith "structured-origin-binding"
    (OriginFormat.protocol (toJson [toJson "P", toJson [toJson ([] : List Json)]])))
  test "structured-origin-kind" (refusedWith "structured-origin-kind"
    (Format.origin .math (ProtocolOrigin.toJson ⟨"P", []⟩)))
  let functionWire := fun (source : Json) (mode : String) => toJson [toJson "function", toJson "main", toJson mode,
    toJson "public", toJson ([] : List Json), toJson ([] : List Json),
    toJson [toJson "protocol", toJson ["P"], toJson ([] : List Json), toJson ([] : List Json)],
    toJson ([] : List Json), source,
    toJson [toJson "block", toJson ([] : List Json), toJson [toJson "return", toJson ([] : List Json)]]]
  test "function decoder required protocol origin" (Format.definition (functionWire leafOrigin.toJson "protocol")).isOk
  test "function decoder refuses legacy absence" (!(Format.definition (functionWire (toJson ([] : List Json)) "protocol")).isOk)
  test "function decoder refuses unknown kind" (!(Format.definition (functionWire leafOrigin.toJson "unknown")).isOk)
  for value in terms do
    let decoded := OriginFormat.term Limits.nesting value.toJson
    test "all closed tree constructors decode" (match decoded with | .ok actual => actual == value | _ => false)
    test "all closed tree constructors admit" (value.valid Limits.nesting)
  test "generic protocol roundtrip" (match OriginFormat.protocol leafOrigin.toJson with
    | .ok value => value == leafOrigin | _ => false)
  test "non generic protocol" (Format.origin .protocol (ProtocolOrigin.toJson ⟨"test::Empty", []⟩)).isOk
  test "full raw snapshot" (check snapshot).isOk
  test "model raw snapshot" (checkFormedPayload snapshot).isOk
  test "Math has no origin" (Format.origin .math (toJson ([] : List Json))).isOk
  test "Local string grammar" (Format.origin .local (toJson [toJson "helper",
    toJson [toJson ["n", "1"]]])).isOk
  for mode in [Kind.protocol, .local] do
    test "absent origin decoder" (!(Format.origin mode (toJson ([] : List Json))).isOk)
    test "absent origin raw admission" (headerRefused none mode)
  test "Math rejects protocol origin raw" (headerRefused (some (.protocol leafOrigin)) .math)
  test "Math rejects Local origin raw" (headerRefused (some (.local "x" [])) .math)
  test "protocol rejects Local origin raw" (headerRefused (some (.local "x" [])))
  test "Local rejects protocol origin raw" (headerRefused (some (.protocol leafOrigin)) .local)
  test "Math rejects metadata decoder" (!(Format.origin .math leafOrigin.toJson).isOk)
  test "Local rejects typed arguments" (!(Format.origin .local leafOrigin.toJson).isOk)
  test "protocol rejects Local string arguments" (!(Format.origin .protocol
    (toJson [toJson "helper", toJson [toJson ["n", "1"]]])).isOk)
  for malformed in ["", "00", "01", "-1", "+1", "1.0", "1e2", " 1", "١", "１", "1_0", repeated 513 '1'] do
    for value in [OriginTerm.natural malformed, .array .unit malformed] do
      test "malformed decimal decoder" (!(OriginFormat.term Limits.nesting value.toJson).isOk)
      test "malformed decimal raw" (headerRefused (some (.protocol ⟨"test::Bad", [("n", value)]⟩)))
  for malformed in [toJson ["unknown"], toJson ["parameter", "T"], toJson ["symbolic", "n"],
      toJson ["bool", "extra"], toJson ["field"], toJson [toJson "nat", toJson (1 : Nat)],
      toJson [toJson "tuple", toJson "not-list"],
      toJson [toJson "nominal", toJson "invalid", toJson "T", toJson ([] : List Json)],
      Json.mkObj [("tag", toJson "unit")]] do
    test "unknown tags arities and shapes" (!(OriginFormat.term Limits.nesting malformed).isOk)
  let duplicate : ProtocolOrigin := ⟨"test::Duplicate", [("n", .natural "1"), ("n", .natural "2")]⟩
  test "duplicate keys decoder" (!(OriginFormat.protocol duplicate.toJson).isOk)
  test "duplicate keys raw" (headerRefused (some (.protocol duplicate)))
  test "duplicate Local keys" (!(Format.origin .local (toJson [toJson "helper",
    toJson [toJson ["n", "1"], toJson ["n", "2"]]])).isOk)
  test "duplicate Local raw" (headerRefused (some (.local "helper" [("n", "1"), ("n", "2")])) .local)
  let ordered : ProtocolOrigin := ⟨"test::Ordered", [("z", .unit), ("a", .index)]⟩
  test "declaration order retained" (match OriginFormat.protocol ordered.toJson with
    | .ok value => value.arguments.map Prod.fst == ["z", "a"] | _ => false)
  for (size, expected) in [(2048, true), (2049, false)] do
    let value : ProtocolOrigin := ⟨repeated size, []⟩
    test "path byte limit decoder" ((OriginFormat.protocol value.toJson).isOk == expected)
    test "path byte limit raw" ((rawSnapshot { leaf with name := "main", origin := some (.protocol value) }).definitions.all Definition.headerValid == expected)
  for (size, expected) in [(1024, true), (1025, false)] do
    let value : ProtocolOrigin := ⟨repeated size 'é', []⟩
    test "UTF8 path byte limit" ((OriginFormat.protocol value.toJson).isOk == expected)
  for path in ["", "a:::b", "a::", "::a", "1a", "a/b", "a b", "a.b"] do
    test "path syntax decoder" (!(OriginFormat.protocol (ProtocolOrigin.toJson ⟨path, []⟩)).isOk)
    test "path syntax raw" (headerRefused (some (.protocol ⟨path, []⟩)))
  for (size, expected) in [(512, true), (513, false)] do
    for value in [OriginTerm.field (repeated size), .group (repeated size),
        .domain (repeated size) "id", .asset "sort" (repeated size),
        .builtin (repeated size) [], .formal (repeated size) [],
        .nominal .record (repeated size) []] do
      test "name byte limit decoder" ((OriginFormat.term Limits.nesting value.toJson).isOk == expected)
      test "name byte limit raw" (value.valid Limits.nesting == expected)
    let value : ProtocolOrigin := ⟨"test::Keys", [(repeated size, .unit)]⟩
    test "key byte limit decoder" ((OriginFormat.protocol value.toJson).isOk == expected)
    test "key byte limit raw" (value.valid == expected)
  for name in ["a::b", "0n", ""] do
    let value : ProtocolOrigin := ⟨"test::Keys", [(name, .unit)]⟩
    test "parameter syntax" (!(OriginFormat.protocol value.toJson).isOk && !value.valid)
  for (depth, expected) in [(63, true), (64, false)] do
    let value := nested depth
    test "term depth decoder" ((OriginFormat.term Limits.nesting value.toJson).isOk == expected)
    test "term depth raw" (value.valid Limits.nesting == expected)
    test "term depth header" (headerRefused (some (.protocol ⟨"test::Depth", [("T", value)]⟩)) == !expected)
  test "standalone term at ordinary lexical boundary" (Format.parse (nested 63).toJson.compress).isOk
  test "standalone origin has no typed-slot exemption" (refusedWith "depth-limit"
    (Format.parse (ProtocolOrigin.toJson ⟨"test::Depth", [("T", nested 63)]⟩).compress))
  for (size, expected) in [(512, true), (513, false)] do
    let children := List.replicate size OriginTerm.unit
    for value in [OriginTerm.tuple children, .nominal .record "test::T" children,
        .builtin "T" children, .formal "T" children] do
      test "child list decoder" ((OriginFormat.term Limits.nesting value.toJson).isOk == expected)
      test "child list raw" (value.valid Limits.nesting == expected)
  for (size, expected) in [(128, true), (129, false)] do
    let value : ProtocolOrigin := ⟨"test::Args", (List.range size).map fun i => ("n" ++ toString i, .unit)⟩
    test "argument limit decoder" ((OriginFormat.protocol value.toJson).isOk == expected)
    test "argument limit raw" (value.valid == expected)
  for (size, expected) in [(511, true), (512, false)] do
    let value : ProtocolOrigin := ⟨"test::Nodes", (List.range 8).map fun i =>
      ("n" ++ toString i, .tuple (List.replicate size .unit))⟩
    test "cumulative term budget decoder" ((OriginFormat.protocol value.toJson).isOk == expected)
    test "cumulative term budget raw" (value.valid == expected)
  -- This explicitly exposes the NFC boundary: different UTF-8 keys remain
  -- different here, although the native frontend refuses the non-NFC key.
  let exact : ProtocolOrigin := ⟨"test::Exact", [("é", .unit), ("é", .unit)]⟩
  test "exact UTF8 keys without normalization" (OriginFormat.protocol exact.toJson).isOk
  let alias := fun term => SourceAlias.mk (.protocol ⟨"test::Alias", [("T", term)]⟩) "symbol" 0
  test "nominal sorts do not collide" (sourceAliasName (alias (.nominal .record "test::T" [])) !=
    sourceAliasName (alias (.nominal .variant "test::T" [])))
  test "formal and builtin do not collide" (sourceAliasName (alias (.formal "T" [])) !=
    sourceAliasName (alias (.builtin "T" [])))
  let .ok aliases := sourceAliases snapshot ["helper"] | throw (IO.userError "valid aliases refused")
  test "Local retained alongside protocols" (aliases.length == 3)
  test "actual protocol index" (aliases.any fun alias => alias.symbol == "main" && alias.index == 1)
  test "protocol ignores helper positions" (match sourceAliases snapshot ["main", "helper", "leaf"] with
    | .ok values => values.any fun alias => alias.symbol == "main" && alias.index == 1 | _ => false)
  test "helper association required" (!(sourceAliases snapshot []).isOk)
  let duplicateOrigin := { snapshot with definitions := [.function leaf,
    .function { leaf with name := "other" }], entry := "leaf", contracts := [⟨"leaf", []⟩, ⟨"other", []⟩] }
  test "ambiguous protocol origin" (refusedWith "root-ambiguous-helper-origin" (sourceAliases duplicateOrigin []))
  let .ok generated := sourceAliasSource "Tests.GeneratedOriginAliases" "Tests.StructuredOriginFixture" snapshot ["helper"]
    | throw (IO.userError "alias source refused")
  IO.FS.createDirAll ".lake/structured-origin"
  IO.FS.writeFile ".lake/structured-origin/GeneratedOriginAliases.lean" generated
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"origin failures: {errors.reverse}")
  IO.println s!"structured-origin: {← count.get} controls passed"

#eval run

end Tests.StructuredOrigin
