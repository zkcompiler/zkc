import Zkc.Source.Structured.Format

/-! Wire-only controls for the one current structured-source schema. These
tests deliberately do not import admission or assign meanings to declarations. -/

set_option autoImplicit false

namespace Tests.StructuredWire
open Lean Zkc.Source.Structured

private def arr (values : List Json) : Json := .arr values.toArray
private def strings (values : List String) : Json := arr (values.map Json.str)
private def numbers (values : List Nat) : Json := arr (values.map toJson)
private def empty : Json := arr []
private def digest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def boolTy : Json := strings ["bool"]
private def fieldTy : Json := strings ["field", scalarDomain]
private def groupTy : Json := strings ["group", groupDomain]
private def serviceTy : Json := strings ["service", scalarServiceContract]

private def ports : Json := arr [
  .str "protocol", strings ["Prover", "Verifier"],
  arr [strings ["Prover"], strings ["Verifier", "Prover"], strings ["Verifier"]],
  arr [strings ["Prover"], strings ["Verifier"]]]

private def relationFields : List Json := [
  .str "relation", .str "Proof", .str "public", .str "opaque.kind",
  .str "opaque/key:007", .str "revision:0009", arr [fieldTy, groupTy, groupTy],
  arr [boolTy], strings ["parameter", "statement", "witness"]]

private def instruction (op : Json) (operands : List Nat := [])
    (results : List Json := []) (regions : List Json := []) (site : String := "") : Json :=
  arr [op, numbers operands, arr results, arr regions, .str site]

private def body (instructions : List Json := []) (terminal : Json :=
    arr [.str "return", numbers []]) : Json :=
  arr [.str "block", arr instructions, terminal]

private def rootFields : List Json := [
  .str "function", .str "main", .str "protocol", .str "public",
  arr [fieldTy, groupTy, serviceTy], arr [boolTy, boolTy], ports, empty, empty,
  body [
    instruction (strings ["group.identity", groupDomain]) [] [groupTy],
    instruction (strings ["group.add", groupDomain]) [0, 2] [groupTy],
    instruction (strings ["group.scale", groupDomain, scalarDomain]) [0, 2] [groupTy],
    instruction (strings ["group.equal", groupDomain]) [0, 1] [boolTy],
    instruction (arr [.str "restrict", strings ["Verifier", "Prover"]]) [0] [boolTy],
    instruction (strings ["exchange", "Prover", "Verifier"]) [0] [boolTy] [] "send.é",
    instruction (strings ["draw", "Verifier", scalarDomain]) [7] [fieldTy] [] "draw/1",
    instruction (arr [.str "statement", .str "Proof", strings ["Verifier", "Prover"],
      toJson (1 : Nat)]) [1, 0]],
]

private def localOrigin : Json := arr [.str "authored::origin", arr [
  strings ["z", "identity/007"], strings ["a", "identity/000"]]]

private def localFields : List Json := [
  .str "function", .str "work", .str "local", .str "private", empty, empty, empty,
  empty, localOrigin, body [] (strings ["stop", "abort", "authored.stop"])]

private def mathFields : List Json := [
  .str "function", .str "formula", .str "math", .str "private", arr [fieldTy],
  arr [fieldTy], empty, arr [arr [.str "index_bound", toJson (0 : Nat), toJson (1 : Nat),
    toJson (0 : Nat)]], empty, body [] (arr [.str "return", numbers [0, 0]])]

private def otherRoot : Json := arr [
  .str "function", .str "other", .str "protocol", .str "private", empty, empty,
  arr [.str "protocol", strings ["Bob", "Alice"], empty, empty], empty, empty, body]

private def domainFields : List Json := [
  .str "domain", .str "items", arr [strings ["vector", scalarDomain]],
  arr [.str "indices", toJson (0 : Nat), toJson (0 : Nat)]]

private def finiteFields : List Json := [
  .str "finite", .str "folded", .str "private", empty, empty,
  .str "items", .str "work", .str ""]

private def envelope (domains relations definitions : List Json) : Json :=
  arr [.str "zkc.structured-source/0", .str "original", .str digest, .str "main",
    arr domains, arr relations, arr definitions]

private def subject : Json := envelope [arr domainFields]
  [arr relationFields, arr (relationFields.set 1 (.str "Unused"))]
  [arr rootFields, otherRoot, arr localFields, arr mathFields, arr finiteFields]

private def decode (json : Json) : Except String Snapshot := do
  Format.snapshot (← Format.parse json.compress)

private def succeeds {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

private def hasError {α : Type} (result : Except String α) (code : String) : Bool :=
  match result with
  | .error actual => actual == code
  | .ok _ => false

example : Format.type (strings ["group", groupDomain]) = .ok (.group groupDomain) := rfl
example : Format.type (strings ["service", scalarServiceContract]) =
    .ok (.service scalarServiceContract) := rfl
example : Format.descriptor (strings ["group.scale", groupDomain, scalarDomain]) =
    .ok (.groupScale groupDomain scalarDomain) := rfl
example : Format.descriptor (arr [.str "statement", .str "Proof", strings ["V", "P"],
    toJson (1 : Nat)]) = .ok (.statement "Proof" ["V", "P"] 1) := rfl

private def run : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let failures ← IO.mkRef ([] : List String)
  let check (label : String) (passed : Bool) : IO Unit := do
    count.modify (· + 1)
    unless passed do failures.modify (label :: ·)

  -- Full text parsing retains declaration order and all opaque metadata.
  match decode subject with
  | .error error => check s!"whole-unit: {error}" false
  | .ok snapshot =>
    check "source-and-entry" (snapshot.source == digest && snapshot.entry == "main")
    check "all-definitions-retained"
      (snapshot.definitions.map Definition.name == ["main", "other", "work", "formula", "folded"])
    check "all-relations-retained" (snapshot.relations.map Relation.name == ["Proof", "Unused"])
    check "domain-retained" (snapshot.domains == [⟨"items", [.vector scalarDomain], .indices 0 0⟩])
    check "relation-exact" (snapshot.relations.head? == some ⟨"Proof", .publicDef, "opaque.kind",
      "opaque/key:007", "revision:0009", [.field scalarDomain, .group groupDomain, .group groupDomain],
      [.boolean], ["parameter", "statement", "witness"]⟩)
    match snapshot.definitions with
    | [.function root, .function other, .function localFn, .function mathFn, .finite finite] =>
      check "protocol-interface-order" (root.interface == some ⟨["Prover", "Verifier"],
        [["Prover"], ["Verifier", "Prover"], ["Verifier"]], [["Prover"], ["Verifier"]]⟩)
      check "protocol-input-types" (root.inputs == [.field scalarDomain, .group groupDomain,
        .service scalarServiceContract])
      check "independent-unused-roster" (other.interface == some ⟨["Bob", "Alice"], [], []⟩)
      check "helper-interfaces" (localFn.interface == none && mathFn.interface == none)
      check "origin-order-and-values" (localFn.origin == some
        ("authored::origin", [("z", "identity/007"), ("a", "identity/000")]))
      check "precondition-retained" (mathFn.preconditions == [⟨0, 1, 0⟩])
      check "finite-retained" (finite.name == "folded" && finite.domain == "items" &&
        finite.step == "work" && finite.predicate == "")
      match localFn.body with
      | .block [] (.stop .abort "authored.stop") => check "stop-site-retained" true
      | _ => check "stop-site-retained" false
      match mathFn.body with
      | .block [] (.ret [0, 0]) => check "repeated-return-references" true
      | _ => check "repeated-return-references" false
      match root.body with
      | .block instructions _ =>
        let actual := instructions.map fun (.instruction op operands results regions site) =>
          (op, operands, results, regions.length, site)
        check "ordered-operations-and-sites" (actual == [
          (.groupIdentity groupDomain, [], [.group groupDomain], 0, ""),
          (.groupAdd groupDomain, [0, 2], [.group groupDomain], 0, ""),
          (.groupScale groupDomain scalarDomain, [0, 2], [.group groupDomain], 0, ""),
          (.groupEqual groupDomain, [0, 1], [.boolean], 0, ""),
          (.restrict ["Verifier", "Prover"], [0], [.boolean], 0, ""),
          (.exchange "Prover" "Verifier", [0], [.boolean], 0, "send.é"),
          (.draw "Verifier" scalarDomain, [7], [.field scalarDomain], 0, "draw/1"),
          (.statement "Proof" ["Verifier", "Prover"] 1, [1, 0], [], 0, "")])
    | _ => check "definition-variants" false

  -- Every supported descriptor and type checks exact arity, including old ones.
  let descriptors : List Json := [
    strings ["field.constant", scalarDomain, "123"],
    strings ["field.add", scalarDomain], strings ["field.subtract", scalarDomain],
    strings ["field.multiply", scalarDomain], strings ["field.equal", scalarDomain],
    strings ["group.identity", groupDomain], strings ["group.add", groupDomain],
    strings ["group.scale", groupDomain, scalarDomain], strings ["group.equal", groupDomain],
    arr [.str "bool.constant", .bool true], strings ["bool.and"], strings ["bool.or"],
    strings ["bool.xor"], strings ["bool.equal"], strings ["bool.not_equal"],
    arr [.str "select", groupTy], strings ["bounded_at", scalarDomain],
    strings ["call", "formula"], strings ["apply", "work"], strings ["local_call", "work", "P"],
    strings ["fold", "items", "step", ""], strings ["if"], strings ["for"],
    strings ["for_condition"], strings ["guard", "P"], arr [.str "restrict", strings ["P", "V"]],
    strings ["exchange", "P", "V"], strings ["draw", "V", scalarDomain],
    arr [.str "statement", .str "Proof", strings ["P", "V"], toJson (0 : Nat)]]
  for op in descriptors do
    check s!"descriptor-valid: {op.compress}" (succeeds (Format.descriptor op))
    if let .arr fields := op then
      check s!"descriptor-extra: {op.compress}" (hasError
        (Format.descriptor (.arr (fields.push .null))) "structured-operation-unsupported")
      check s!"descriptor-missing: {op.compress}" (hasError
        (Format.descriptor (arr (fields.toList.take (fields.size - 1)))) "structured-operation-unsupported")
  for ty in [boolTy, strings ["index"], fieldTy, strings ["vector", scalarDomain], groupTy, serviceTy] do
    check s!"type-valid: {ty.compress}" (succeeds (Format.type ty))
    if let .arr fields := ty then
      check s!"type-extra: {ty.compress}" (hasError
        (Format.type (.arr (fields.push .null))) "structured-type-unsupported")
      check s!"type-missing: {ty.compress}" (hasError
        (Format.type (arr (fields.toList.take (fields.size - 1)))) "structured-type-unsupported")

  for (label, fields, decoder, code) in [
      ("function", rootFields, fun j => succeeds (Format.definition j), "structured-definition"),
      ("finite", finiteFields, fun j => succeeds (Format.definition j), "structured-definition"),
      ("relation", relationFields, fun j => succeeds (Format.relation j), "structured-relation"),
      ("domain", domainFields, fun j => succeeds (Format.domain j), "structured-domain")] do
    check s!"record-valid: {label}" (decoder (arr fields))
    for malformed in [fields ++ [.null], fields.take (fields.length - 1)] do
      let actual := if label == "relation" then Format.relation (arr malformed) |>.map (fun _ => ())
        else if label == "domain" then Format.domain (arr malformed) |>.map (fun _ => ())
        else Format.definition (arr malformed) |>.map (fun _ => ())
      check s!"record-arity: {label}" (hasError actual code)

  for (label, value, code) in [
      ("unknown-type", strings ["tuple"], "structured-type-unsupported"),
      ("group-domain", strings ["group", scalarDomain], "structured-group-domain"),
      ("field-domain", strings ["field", groupDomain], "structured-field-domain"),
      ("service-version", strings ["service", "random.bls12-381.fr/1"], "structured-service-contract"),
      ("service-other-field", strings ["service", "random.other/0"], "structured-service-contract"),
      ("service-empty", strings ["service", ""], "structured-string"),
      ("type-not-array", .str "bool", "structured-array")] do
    check label (hasError (Format.type value) code)

  for (label, value, code) in [
      ("unknown-operation", strings ["group.subtract", groupDomain], "structured-operation-unsupported"),
      ("scale-swapped-domains", strings ["group.scale", scalarDomain, groupDomain], "structured-group-domain"),
      ("scale-wrong-field", strings ["group.scale", groupDomain, groupDomain], "structured-field-domain"),
      ("draw-wrong-field", strings ["draw", "V", groupDomain], "structured-field-domain"),
      ("exchange-empty-owner", strings ["exchange", "", "V"], "structured-string"),
      ("draw-empty-owner", strings ["draw", "", scalarDomain], "structured-string"),
      ("restrict-not-array", strings ["restrict", "P"], "structured-array"),
      ("restrict-empty-name", arr [.str "restrict", strings [""]], "structured-string"),
      ("restrict-role-capacity", arr [.str "restrict", strings (List.replicate 17 "P")], "structured-list-limit"),
      ("statement-selector-shape", arr [.str "statement", .str "R", .str "P", toJson (0 : Nat)], "structured-array"),
      ("statement-acceptance-string", arr [.str "statement", .str "R", empty, .str "0"], "structured-natural"),
      ("statement-acceptance-bool", arr [.str "statement", .str "R", empty, .bool false], "structured-natural"),
      ("statement-acceptance-limit", arr [.str "statement", .str "R", empty, toJson (4097 : Nat)], "structured-number-limit"),
      ("statement-empty-relation", arr [.str "statement", .str "", empty, toJson (0 : Nat)], "structured-string"),
      ("bool-not-boolean", arr [.str "bool.constant", toJson (1 : Nat)], "structured-operation-unsupported")
    ] do
    check label (hasError (Format.descriptor value) code)

  for (label, value, code) in [
      ("interface-tag", arr [.str "math", empty, empty, empty], "structured-interface"),
      ("interface-missing", arr [.str "protocol", empty, empty], "structured-interface"),
      ("interface-extra", arr [.str "protocol", empty, empty, empty, empty], "structured-interface"),
      ("interface-null", .null, "structured-array"),
      ("roster-not-array", arr [.str "protocol", .str "P", empty, empty], "structured-array"),
      ("roster-empty-name", arr [.str "protocol", strings [""], empty, empty], "structured-string"),
      ("roster-capacity", arr [.str "protocol", strings (List.replicate 17 "P"), empty, empty], "structured-list-limit"),
      ("scope-not-array", arr [.str "protocol", strings ["P"], strings ["P"], empty], "structured-array"),
      ("scope-empty-name", arr [.str "protocol", strings ["P"], arr [strings [""]], empty], "structured-string"),
      ("scope-capacity", arr [.str "protocol", strings ["P"], arr [strings (List.replicate 17 "P")], empty], "structured-list-limit"),
      ("ports-capacity", arr [.str "protocol", strings ["P"], arr (List.replicate 513 empty), empty], "structured-list-limit")
    ] do
    check label (hasError (Format.interface value) code)

  for badPurpose in ["", "Parameter", "public", "unknown"] do
    check s!"relation-purpose: {badPurpose}" (hasError
      (Format.relation (arr (relationFields.set 8 (strings [badPurpose])))) "structured-relation-purpose")
  for index in [1, 3, 4, 5] do
    check s!"relation-empty-string: {index}" (hasError
      (Format.relation (arr (relationFields.set index (.str "")))) "structured-string")
  check "relation-purpose-type" (hasError
    (Format.relation (arr (relationFields.set 8 (arr [.null])))) "structured-relation-purpose")
  check "relation-visibility" (hasError
    (Format.relation (arr (relationFields.set 2 (.str "export")))) "structured-visibility")
  check "relation-not-a-definition" (hasError (Format.definition (arr relationFields)) "structured-definition")
  check "function-not-a-relation" (hasError (Format.relation (arr rootFields)) "structured-relation")
  check "legacy-function" (hasError
    (Format.definition (arr (rootFields.take 6 ++ rootFields.drop 7))) "structured-definition")
  check "legacy-role-envelope" (hasError (decode (arr [.str "zkc.structured-source/0",
    .str "original", .str digest, .str "main", .str "P", empty, empty])) "structured-array")
  for envelopeFields in [
      [.str "zkc.structured-source/1", .str "original", .str digest, .str "main", empty, empty, empty],
      [.str "zkc.structured-source/0", .str "projected", .str digest, .str "main", empty, empty, empty],
      [.str "zkc.structured-source/0", .str "original", .str digest, .str "main", empty, empty],
      [.str "zkc.structured-source/0", .str "original", .str digest, .str "main", empty, empty, empty, empty]] do
    check "envelope-tag-or-arity" (hasError (decode (arr envelopeFields)) "structured-envelope")
  for badDigest in ["sha256:" ++ String.ofList (List.replicate 64 'A'),
      "sha256:" ++ String.ofList (List.replicate 64 'g'), "sha256:0", "SHA256:" ++
        String.ofList (List.replicate 64 '0')] do
    check "digest-canonical" (hasError (decode (arr [.str "zkc.structured-source/0",
      .str "original", .str badDigest, .str "main", empty, empty, empty])) "structured-source-digest")

  -- Bounded shapes apply to all declarations, even unused metadata and bodies.
  for (label, value) in [
      ("domains-capacity", envelope (List.replicate 129 (arr domainFields)) [] []),
      ("relations-capacity", envelope [] (List.replicate 129 (arr relationFields)) []),
      ("definitions-capacity", envelope [] [] (List.replicate 129 (arr rootFields))),
      ("unused-relation-purpose", envelope [] [arr (relationFields.set 8 (strings ["bad"]))] [arr rootFields]),
      ("unused-helper-type", envelope [] [] [arr rootFields, arr (mathFields.set 4 (arr [strings ["unknown"]]))])
    ] do
    let expected := if label == "unused-relation-purpose" then "structured-relation-purpose"
      else if label == "unused-helper-type" then "structured-type-unsupported"
      else "structured-list-limit"
    check label (hasError (decode value) expected)
  check "signature-capacity" (hasError (Format.types (arr (List.replicate 513 boolTy))) "structured-list-limit")
  check "references-capacity" (hasError (Format.refs (numbers (List.replicate 513 0))) "structured-list-limit")
  check "reference-number-capacity" (hasError (Format.refs (numbers [4097])) "structured-number-limit")
  check "instruction-capacity" (hasError
    (Format.block 64 (body (List.replicate 4097 (instruction (strings ["if"]))))) "structured-list-limit")
  check "region-count-capacity" (hasError
    (Format.block 64 (body [instruction (strings ["if"]) [] [] [empty, empty, empty]])) "structured-list-limit")
  check "region-shape" (hasError
    (Format.block 64 (body [instruction (strings ["if"]) [] [] [empty]])) "structured-region")
  check "instruction-shape" (hasError
    (Format.block 64 (arr [.str "block", arr [empty], arr [.str "return", empty]])) "structured-instruction")
  check "block-shape" (hasError (Format.block 64 (arr [.str "block", empty])) "structured-block")
  check "region-depth" (hasError (Format.block 0 body) "structured-region-depth")
  let nested := body [instruction (strings ["if"]) [] [] [arr [empty, empty, body]]]
  check "nested-region-depth" (hasError (Format.block 1 nested) "structured-region-depth")
  check "nested-region-accepted" (succeeds (Format.block 2 nested))
  check "origin-shape" (hasError (Format.origin (arr [.str "origin"])) "structured-origin")
  check "origin-binding-shape" (hasError
    (Format.origin (arr [.str "origin", arr [strings ["key"]]])) "structured-origin-binding")
  check "origin-binding-capacity" (hasError
    (Format.origin (arr [.str "origin", arr (List.replicate 129 (strings ["key", "value"]))])) "structured-list-limit")
  check "domain-constructor" (hasError
    (Format.domain (arr (domainFields.set 3 (strings ["unknown"])))) "structured-domain-constructor")
  check "domain-axis" (hasError (Format.domain (arr (domainFields.set 3
    (arr [.str "indices", toJson (0 : Nat), toJson (1 : Nat)])))) "structured-number-limit")
  check "precondition-shape" (hasError (Format.bound (strings ["unknown"])) "structured-precondition")
  check "precondition-axis" (hasError (Format.bound
    (arr [.str "index_bound", toJson (0 : Nat), toJson (1 : Nat), toJson (1 : Nat)])) "structured-number-limit")
  check "kind-unknown" (hasError (Format.kind (.str "helper")) "structured-kind")
  check "terminator-unknown" (hasError (Format.terminator (strings ["exit"])) "structured-terminator")
  check "stop-unknown" (hasError (Format.terminator (strings ["stop", "error", "site"])) "structured-stop")
  check "stop-empty-site" (hasError (Format.terminator (strings ["stop", "reject", ""])) "structured-string")
  for reason in ["reject", "abort", "exhausted", "incomplete", "refused"] do
    check s!"stop-retained: {reason}" (succeeds (Format.terminator (strings ["stop", reason, "site"])))

  for text in ["00", "01", "-1", "+1", " 1", "1 ", "1.0", "1e0", "١", "１２"] do
    check s!"constant-canonical: {text}" (hasError
      (Format.descriptor (strings ["field.constant", scalarDomain, text])) "structured-decimal")
  check "constant-modulus" (hasError
    (Format.descriptor (strings ["field.constant", scalarDomain, toString scalarModulus])) "structured-field-canonical")
  for value in [0, scalarModulus - 1] do
    check "constant-boundary" (succeeds (Format.descriptor (strings ["field.constant", scalarDomain, toString value])))
  let utf8Boundary := String.ofList (List.replicate 256 'é')
  check "string-512-bytes" (succeeds (Format.string (.str utf8Boundary)))
  check "string-513-bytes" (hasError (Format.string (.str (utf8Boundary ++ "a"))) "structured-string")
  check "empty-string" (hasError (Format.string (.str "")) "structured-string")
  check "string-wrong-type" (hasError (Format.string .null) "structured-string")

  for (text, code) in [
      ("[", "invalid-json"), ("[] []", "invalid-json"), ("[0,]", "invalid-json"),
      ("[01]", "invalid-json"), ("[-0]", "expected-natural"), ("[-1]", "expected-natural"),
      ("[1.0]", "expected-natural"), ("[1e2]", "expected-natural"),
      ("[1E999999]", "expected-natural"), ("{}", "invalid-shape"),
      ("[{}]", "invalid-shape"), ("{\"x\":1,\"x\":2}", "invalid-shape"),
      ("[" ++ String.ofList (List.replicate 1025 '9') ++ "]", "number-limit"),
      (String.ofList (List.replicate 65 '[') ++ String.ofList (List.replicate 65 ']'), "depth-limit"),
      (String.ofList (List.replicate (1024 * 1024 + 1) ' '), "byte-limit")
    ] do
    check s!"lexical-error: {code}" (hasError (Format.parse text (1024 * 1024)) code)
  check "depth-64-boundary" (succeeds (Format.parse
    (String.ofList (List.replicate 64 '[') ++ String.ofList (List.replicate 64 ']'))))
  check "byte-boundary" (succeeds (Format.parse
    ("[]" ++ String.ofList (List.replicate (1024 * 1024 - 2) ' ')) (1024 * 1024)))
  for text in ["[-{}eE.123]", "quote\"backslash\\", String.ofList (List.replicate 65 '['),
      String.ofList (List.replicate 1025 '9')] do
    check "lexical-punctuation-inside-strings" (succeeds (Format.parse (Json.str text).compress))

  -- These are well-shaped wire records, not successful semantic admission.
  -- Never sort, deduplicate, or infer a relation/formula binding in the decoder.
  check "duplicate-roster-retained" (succeeds
    (Format.interface (arr [.str "protocol", strings ["P", "P"], empty, empty])))
  check "unresolved-scope-retained" (succeeds
    (Format.interface (arr [.str "protocol", strings ["P"], arr [strings ["Q"]], empty])))
  check "empty-roster-deferred" (succeeds (Format.interface (arr [.str "protocol", empty, empty, empty])))
  check "interface-kind-consistency-deferred" (succeeds
    (Format.definition (arr (mathFields.set 6 ports))))
  check "relation-signature-deferred" (succeeds
    (Format.relation (arr (relationFields.set 7 (arr [fieldTy])))))
  check "duplicate-origin-retained" (succeeds
    (Format.origin (arr [.str "origin", arr [strings ["k", "a"], strings ["k", "b"]]])))
  let errors ← failures.get
  unless errors.isEmpty do
    for error in errors.reverse do IO.eprintln s!"structured wire failed: {error}"
    throw (IO.userError s!"structured wire: {errors.length} / {← count.get} checks failed")
  IO.println s!"structured wire: {← count.get} checks passed"

#eval run
end Tests.StructuredWire
