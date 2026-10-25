import Tests.StructuredOriginFixture

/-! Exact reader depth controls. Full authored snapshots exercise parsing,
snapshot decoding and admission; these are not native correspondence proofs. -/
set_option autoImplicit false
open Lean Zkc.Source.Structured

namespace Tests.StructuredOriginDepth

private def arr (values : List Json) : Json := .arr values.toArray
private def empty : Json := arr []
private def nest (wrap : OriginTerm → OriginTerm) : Nat → OriginTerm → OriginTerm
  | 0, leaf => leaf
  | n + 1, leaf => wrap (nest wrap n leaf)

private def brackets : Nat → Json
  | 0 => .null
  | n + 1 => arr [brackets n]

private def arrayDepth : Nat → Json → Nat
  | 0, _ => 0
  | fuel + 1, .arr values => 1 + values.foldl (fun depth value => max depth (arrayDepth fuel value)) 0
  | _, _ => 0

private def body : Json := arr [.str "block", empty, arr [.str "return", empty]]
private def function (source : Json) : Json := arr [.str "function", .str "main", .str "protocol",
  .str "public", empty, empty, arr [.str "protocol", arr [.str "P"], empty, empty],
  empty, source, body]
private def envelope (definitions : List Json) : Json := arr [.str "zkc.structured-source/0",
  .str "original", .str ("sha256:" ++ String.ofList (List.replicate 64 '0')), .str "main",
  empty, empty, empty, arr definitions, arr [arr [.str "main", empty]], arr [empty, empty]]
private def wire (origin : ProtocolOrigin) : Json := envelope [function origin.toJson]
private def withTerm (term : OriginTerm) : ProtocolOrigin := ⟨"test::Depth", [("T", term)]⟩
private def replace (json : Json) (index : Nat) (value : Json) : Json :=
  match json with
  | .arr values => .arr (values.set! index value)
  | _ => json
private def refusedWith {α : Type} (code : String) : Except String α → Bool
  | .error actual => actual == code
  | .ok _ => false
private def snapshotText (json : Json) : Except String Snapshot := do
  Format.snapshot (← Format.parse json.compress)

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let good := withTerm .unit
  let deepest := withTerm (nest (fun t => .tuple [t]) 63 (.tuple []))
  test "pre-parser capacity is exactly 134" (Limits.parsedNesting == 134)
  test "full valid origin reaches exactly 134 arrays" (arrayDepth 200 (wire deepest) == 134)
  let firstTooWide := wire (withTerm (nest (fun t => .tuple [t]) 64 .unit))
  test "65 tuple levels reach exactly 135 arrays" (arrayDepth 200 firstTooWide == 135)
  test "135-array typed origin refused before parsing" (refusedWith "depth-limit"
    (Format.parse firstTooWide.compress))
  -- The empty children array of the final tuple reaches bracket depth 134.
  for wrap in [(fun t => OriginTerm.array t "1"), (fun t => .tuple [t]),
      (fun t => .nominal .record "test::T" [t]), (fun t => .builtin "T" [t]),
      (fun t => .formal "T" [t])] do
    let origin := withTerm (nest wrap 63 (.tuple []))
    let json := wire origin
    test "64 typed levels strict origin decoder" (OriginFormat.protocol origin.toJson).isOk
    test "64 typed levels full snapshot decoder" (Format.snapshot json).isOk
    test "64 typed levels full text parser" (Format.parse json.compress).isOk
    test "64 typed levels full text snapshot" (snapshotText json).isOk
    test "64 typed levels full text admission" (decode json.compress).isOk
    test "exact origin retained through text" (match snapshotText json with
      | .ok value => value.definitions.any fun d => match d with
        | .function f => f.origin == some (.protocol origin)
        | _ => false
      | _ => false)
    let tooDeep := withTerm (nest wrap 64 .unit)
    test "65 typed levels origin refusal" (refusedWith "structured-origin-depth"
      (OriginFormat.protocol tooDeep.toJson))
    test "65 typed levels snapshot refusal" (refusedWith "structured-origin-depth"
      (Format.snapshot (wire tooDeep)))
    test "65 typed levels text admission refused" (!(decode (wire tooDeep).compress).isOk)
  let narrowTooDeep := wire (withTerm (nest (fun t => .array t "1") 64 .unit))
  test "typed depth refused below pre-parser capacity" (refusedWith "structured-origin-depth"
    (Format.parse narrowTooDeep.compress))
  for depth in [63, 64, 65] do
    test s!"ordinary standalone lexical depth {depth}"
      ((Format.parse (brackets depth).compress).isOk == (depth ≤ 64))
    let row := replace (function deepest.toJson) 9 (brackets (depth - 3))
    test s!"full envelope body has exact lexical depth {depth}"
      (arrayDepth 200 (envelope [replace row 8 good.toJson]) == depth)
    test s!"ordinary body lexical depth {depth} with deep origin"
      ((Format.parse (envelope [row]).compress).isOk == (depth ≤ 64))
  test "standalone origin has no exemption" (refusedWith "depth-limit"
    (Format.parse deepest.toJson.compress))
  test "standalone protocol row has no exemption" (refusedWith "depth-limit"
    (Format.parse (function deepest.toJson).compress))
  let row := function deepest.toJson
  let json := wire deepest
  for (name, malformed) in [("wrong version", replace json 0 (.str "zkc.structured-source/1")),
      ("wrong stage", replace json 1 (.str "prepared")),
      ("short envelope", match json with | .arr v => .arr v.pop | _ => json),
      ("long envelope", match json with | .arr v => .arr (v.push .null) | _ => json),
      ("wrong definitions slot", replace (replace json 7 empty) 6 (arr [row])),
      ("extra definitions wrapper", replace json 7 (arr [arr [row]])),
      ("wrong row tag", envelope [replace row 0 (.str "finite")]),
      ("unknown kind", envelope [replace row 2 (.str "unknown")]),
      ("Math kind", envelope [replace row 2 (.str "math")]),
      ("Local kind", envelope [replace row 2 (.str "local")]),
      ("short row", envelope [match row with | .arr v => .arr v.pop | _ => row]),
      ("long row", envelope [match row with | .arr v => .arr (v.push .null) | _ => row]),
      ("origin in ordinary body", envelope [replace (function good.toJson) 9 deepest.toJson]),
      ("origin in wrong row slot", envelope [replace (replace row 8 good.toJson) 7 deepest.toJson])] do
    test s!"no malformed-envelope exemption: {name}" (refusedWith "depth-limit" (Format.parse malformed.compress))
    test s!"no malformed-envelope admission: {name}" (!(decode malformed.compress).isOk)
  -- Every other ordinary top-level and function slot still counts the full
  -- containing envelope depth. The definitions table is checked row by row.
  for index in [0, 1, 2, 3, 4, 5, 6, 8, 9] do
    test s!"ordinary envelope slot {index}" (refusedWith "depth-limit"
      (Format.parse (replace json index (brackets 64)).compress))
  for index in [0, 1, 2, 3, 4, 5, 6, 7, 9] do
    test s!"ordinary function slot {index}" (refusedWith "depth-limit"
      (Format.parse (envelope [replace row index (brackets 62)]).compress))
  test "unused deep protocol origin accepted" (Format.parse (envelope [function good.toJson,
    replace row 1 (.str "unused")]).compress).isOk
  test "unused ordinary body cannot exceed lexical depth 64" (refusedWith "depth-limit"
    (Format.parse (envelope [function good.toJson,
      replace (replace row 1 (.str "unused")) 9 (brackets 62)]).compress))
  test "unused malformed origin refused" (refusedWith "structured-origin-term" (Format.parse
    (envelope [function good.toJson, replace (replace row 1 (.str "unused")) 8
      (arr [.str "test::Bad", arr [arr [.str "T", arr [.str "unknown"]]]])]).compress))
  test "body depth cannot hide behind malformed origin" (!(Format.parse (envelope [
    replace (replace row 8 empty) 9 (brackets 62)]).compress).isOk)
  -- parse checks resource bounds, not all schema fields. Other malformed
  -- fields still fail snapshot decoding, even with a strictly valid deep origin.
  for index in [2, 3, 4, 5, 6, 8, 9] do
    test s!"shallow malformed envelope field {index} cannot admit"
      (!(snapshotText (replace json index .null)).isOk)
  for index in [1, 3, 4, 5, 6, 7, 9] do
    test s!"shallow malformed function field {index} cannot admit"
      (!(snapshotText (envelope [replace row index .null])).isOk)
  for (size, expected) in [(128, true), (129, false)] do
    let origin : ProtocolOrigin := ⟨"test::Args", (List.range size).map fun i => ("n" ++ toString i, .unit)⟩
    test "argument limit full snapshot" ((Format.snapshot (wire origin)).isOk == expected)
    test "argument limit full text" ((snapshotText (wire origin)).isOk == expected)
  for (size, expected) in [(512, true), (513, false)] do
    for value in [OriginTerm.tuple (List.replicate size .unit),
        .nominal .record "test::T" (List.replicate size .unit),
        .builtin "T" (List.replicate size .unit), .formal "T" (List.replicate size .unit)] do
      test "child limit full snapshot" ((Format.snapshot (wire (withTerm value))).isOk == expected)
      test "child limit full text" ((snapshotText (wire (withTerm value))).isOk == expected)
  for (lastSize, expected) in [(511, true), (512, false)] do
    let origin : ProtocolOrigin := ⟨"test::Nodes", (List.range 8).map fun i =>
      ("n" ++ toString i, .tuple (List.replicate (if i == 7 then lastSize else 511) .unit))⟩
    test "4096 versus 4097 terms full snapshot" ((Format.snapshot (wire origin)).isOk == expected)
    test "4096 versus 4097 terms full text" ((snapshotText (wire origin)).isOk == expected)
    test "4096 versus 4097 terms full admission" ((decode (wire origin).compress).isOk == expected)
  for bad in [empty, arr [.str "test::Bad", arr [arr [.str "T", brackets 80]]],
      arr [.str "test::Bad", arr [arr [.str "T", arr [.str "unit"]], arr [.str "T", arr [.str "unit"]]]]] do
    test "exempt slot must strictly decode" (!(Format.parse (envelope [function bad]).compress).isOk)
  for (size, expected) in [(128, true), (129, false)] do
    test "definitions table limit unchanged" ((snapshotText (envelope
      (List.replicate size (function good.toJson)))).isOk == expected)
  let opens := fun n => String.ofList (List.replicate n '[')
  test "134 arrays reach JSON syntax guard" (refusedWith "invalid-json" (Format.parse (opens 134 ++ "!")))
  test "135 arrays refused before JSON syntax guard" (refusedWith "depth-limit" (Format.parse (opens 135 ++ "!")))
  test "malicious arbitrary nesting refused" (refusedWith "depth-limit" (Format.parse (opens 10000)))
  test "quoted brackets and escapes do not consume depth"
    (Format.parse (arr [.str (opens 1000 ++ "\"\\")]).compress).isOk
  test "object preflight unchanged" (refusedWith "invalid-shape" (Format.parse "{}"))
  test "negative preflight unchanged" (refusedWith "expected-natural" (Format.parse "[-1]"))
  test "numeric token guard unchanged" (refusedWith "number-limit"
    (Format.parse (String.ofList (List.replicate 1025 '1'))))
  test "exponent guard unchanged" (refusedWith "expected-natural" (Format.parse "[1e2]"))
  test "custom byte guard unchanged" (refusedWith "byte-limit" (Format.parse "[[]]" 3))
  test "scalar parser accepts 134 arrays" (Zkc.Source.Format.parse 1000 (brackets 134).compress).isOk
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"origin depth failures: {errors.reverse}")
  IO.println s!"structured-origin-depth: {← count.get} controls passed"

#eval run

end Tests.StructuredOriginDepth
