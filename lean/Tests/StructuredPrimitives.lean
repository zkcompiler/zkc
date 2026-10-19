import Zkc.Source.Structured.Import
import Zkc.Source.Structured.PrimitiveLaws
import Mathlib.Data.ZMod.Basic

/-! Independent direct-constructor and wire controls. These authored controls
are not represented as original native source captures. -/

open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredPrimitives

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def root : Definition := .function ⟨"main", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], none, .block [] (.ret [])⟩
private def snapshot (bindings : List Binding) (defs : List Definition := [root]) : Snapshot :=
  (let contractDefinitions : List Definition := defs
   ⟨digest, "main", [], [], bindings, contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows⟩)
private def binding (contract : String) (arguments : List String := []) : Binding :=
  ⟨"primitive", contract, arguments, ""⟩
private def localHelper (op : Descriptor) (inputs outputs : List Ty) (site : String := "exec")
    (regions : List WireRegion := []) (kind : Kind := .local) : Definition :=
  .function ⟨"work", kind, .privateDef, inputs, outputs, none, [],
    if kind == .local then some ("work", []) else none,
    .block [.instruction op (List.range inputs.length) outputs regions site]
      (.ret (List.range outputs.length))⟩
private def refusedWith {α : Type} (result : Except String α) (code : String) : Bool :=
  match result with
  | .error actual => actual == code
  | .ok _ => false
private def admits (bindings : List Binding) (defs : List Definition := [root]) : Bool :=
  (check (snapshot bindings defs)).isOk
private def arr (values : List Json) : Json := .arr values.toArray
private def strings (values : List String) : Json := arr (values.map Json.str)
private def bindingWire (b : Binding) : Json := arr [
  .str "binding", .str b.name, .str b.contract, strings b.arguments, .str b.implementation]

private def catalogue : List (String × String × List String × Primitive) := [
  ("index_constant", "index.constant", [], .indexConstant 0),
  ("index_equal", "index.equal", [], .indexEqual),
  ("index_less", "index.less", [], .indexLess),
  ("index_add", "index.add", [], .indexAdd),
  ("index_mul", "index.mul", [], .indexMul),
  ("index_sub", "index.sub", [], .indexSub),
  ("index_div", "index.div", [], .indexDiv),
  ("index_mod", "index.mod", [], .indexMod),
  ("vector_empty", "vector.empty", [scalarDomain], .vectorEmpty scalarDomain),
  ("vector_length", "vector.length", [scalarDomain], .vectorLength scalarDomain),
  ("vector_sum", "vector.sum", [scalarDomain], .vectorSum scalarDomain),
  ("vector_split", "vector.split", [scalarDomain], .vectorSplit scalarDomain),
  ("vector_append", "vector.append", [scalarDomain], .vectorAppend scalarDomain),
  ("vector_equal", "vector.equal", [scalarDomain], .vectorEqual scalarDomain),
  ("field_equal", "field.equal", [scalarDomain], .fieldEqual scalarDomain)]

private abbrev F := ZMod 97
private def scalarIndex (p : Primitive) (args : Values (assignment F F) p.arguments) :
    Option Nat := match p, p.evaluate args with
  | .indexConstant _, .returned (.cons n .nil)
  | .indexAdd, .returned (.cons n .nil)
  | .indexMul, .returned (.cons n .nil)
  | .indexSub, .returned (.cons n .nil)
  | .indexDiv, .returned (.cons n .nil)
  | .indexMod, .returned (.cons n .nil) => some n
  | _, _ => none

private def stopped {A : Type} (outcome : PIR.Outcome A) (reason : PIR.Stop) : Bool :=
  match outcome with | .stopped actual => actual == reason | _ => false

-- Kernel controls for full ordered split, append duplicates and shape failure.
example : Primitive.evaluate (F := F) (G := F) (.vectorSplit scalarDomain)
    (.cons [1, 7, 2, 9] .nil) = .returned (.cons [1, 7] (.cons [2, 9] .nil)) := rfl
example : Primitive.evaluate (F := F) (G := F) (.vectorSplit scalarDomain)
    (.cons [1, 2, 3, 4, 5, 6] .nil) = .returned (.cons [1, 2, 3] (.cons [4, 5, 6] .nil)) := rfl
example : Primitive.evaluate (F := F) (G := F) (.vectorAppend scalarDomain)
    (.cons [3, 3] (.cons 8 .nil)) = .returned (.cons [3, 3, 8] .nil) := rfl
example : Primitive.evaluate (F := F) (G := F) .indexDiv
    (.cons 8 (.cons 0 .nil)) = .stopped .refused := rfl

-- A checked primitive executes even when its single result is discarded and
-- the enclosing region returns zero results.
private def discardedDivision : Region dialect [.index, .index] [] :=
  .letOp (.exec .indexDiv) (.cons .here (.cons (.there .here) .nil)) .nil (.ret .nil)

example : discardedDivision.denote (meaning F F [])
    (Values.cons 8 (.cons 0 .nil)).get = .halt .refused := rfl

example : discardedDivision.component (meaning F F [])
    (Evaluation.componentOperation SiteObservations.closed ⟨[], []⟩)
    (Values.cons (some 8) (.cons none .nil)).get = .halt .incomplete := rfl

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  for (native, contract, domains, primitive) in catalogue do
    let b := binding contract domains
    let parameters := if native == "index_constant" then ["0"] else []
    let descriptor := Descriptor.exec ("algebra.exec." ++ native) b.name parameters
    let helper := localHelper descriptor primitive.arguments primitive.results
    test (contract ++ ":unused") (admits [b])
    test (contract ++ ":wire") ((Format.binding (bindingWire b)).isOk)
    test (contract ++ ":typed") (admits [b] [root, helper])
    test (contract ++ ":missing-site") (!admits [b] [root,
      localHelper descriptor primitive.arguments primitive.results ""])
    test (contract ++ ":math-owner") (!admits [b] [root,
      localHelper descriptor primitive.arguments primitive.results "" [] .math])
    test (contract ++ ":extra-parameter") (!(resolvePrimitive (snapshot [b])
      ("algebra.exec." ++ native) b.name (parameters ++ ["0"])).isOk)
    test (contract ++ ":wrong-signature") (!admits [b] [root,
      localHelper descriptor primitive.arguments (primitive.results ++ [.boolean])])
  for name in ["", "1bad", "a/b", "é", "a b", String.ofList (List.replicate 257 'a')] do
    let b := { binding "index.add" with name }
    test ("name:" ++ name.take 10) (!admits [b] && !(Format.binding (bindingWire b)).isOk)
  test "name-256" (admits [{binding "index.add" with name := String.ofList (List.replicate 256 'a')}])
  test "name-punctuation" (admits [{binding "index.add" with name := "_A.0-b"}])
  for bad in [binding "unknown", binding "vector.product" [scalarDomain],
      binding "index.add" [scalarDomain], binding "vector.split",
      binding "field.equal" [scalarDomain, scalarDomain],
      {binding "index.add" with implementation := "native/index.add"}] do
    test ("invalid-unused:" ++ bad.contract) (!admits [bad] && !(Format.binding (bindingWire bad)).isOk)
  -- A root is resolved against the unit's catalogue rows, even when unused.
  for (bad, code) in [(binding "vector.sum" [groupDomain], "structured-domain-sort"),
      (binding "field.equal" ["koala-bear"], "structured-domain-unknown")] do
    test ("unresolved-root:" ++ bad.contract) (!admits [bad] &&
      (Format.binding (bindingWire bad)).isOk &&
      refusedWith (bad.resolveRoot blsRows) code)
  let fieldOnly : Catalogue := ⟨[⟨"f", .field, [], ["Field"], some 5⟩], [], []⟩
  test "root-capability" (refusedWith ((binding "vector.equal" ["f"]).resolveRoot fieldOnly)
    "structured-domain-capability")
  test "root-field" ((binding "vector.sum" ["f"]).resolveRoot fieldOnly matches .ok "f")
  let envelope := [Json.str "zkc.structured-source/0", .str "original", .str digest,
    .str "main", arr [], arr [], arr [], arr [], arr [], arr [arr [], arr []]]
  test "wire-ten-fields" ((Format.snapshot (arr envelope)).isOk)
  test "wire-no-old-envelope" (!(Format.snapshot (arr (envelope.take 9))).isOk)
  test "wire-no-extra-envelope" (!(Format.snapshot (arr (envelope ++ [arr []]))).isOk)
  test "wire-unused-bad-binding" (!(Format.snapshot (arr (envelope.set 6
    (arr [bindingWire (binding "vector.product" [scalarDomain])])))).isOk)
  test "wire-no-short-binding" (!(Format.binding (strings ["binding", "b", "index.add"])).isOk)
  test "wire-no-extra-binding" (!(Format.binding (arr [
    .str "binding", .str "b", .str "index.add", arr [], .str "", .str "extra"])).isOk)
  test "wire-no-execute-tag" (!(Format.descriptor (arr [
    .str "execute", .str "algebra.exec.index_add", .str "b", arr []])).isOk)
  test "wire-exec-arity" (!(Format.descriptor (strings ["exec", "algebra.exec.index_add", "b"])).isOk)
  test "duplicate" (!admits [binding "index.add", binding "index.add"])
  test "namespace" (!admits [{binding "index.add" with name := "main"}])
  test "bindings-not-entry" (!(check {snapshot [binding "index.add"] with entry := "primitive"}).isOk)
  test "bindings-not-callable" (!admits [binding "index.add"] [root,
    localHelper (.apply "primitive") [] []])
  test "binding-limit-128" (admits ((List.range 128).map fun i =>
    {binding "index.add" with name := "b" ++ toString i}))
  test "binding-limit-129" (!admits ((List.range 129).map fun i =>
    {binding "index.add" with name := "b" ++ toString i}))
  test "kind-contract-mismatch" (!(resolvePrimitive (snapshot [binding "index.add"])
    "algebra.exec.index_mul" "primitive" []).isOk)
  test "native-name-exact" (!(resolvePrimitive (snapshot [binding "index.add"])
    "index_add" "primitive" []).isOk)
  for text in ["00", "+1", "-1", "1 ", " 1", "18446744073709551616", "١", ""] do
    test ("index-decimal:" ++ text) (!(Format.indexDecimal text).isOk &&
      !(resolvePrimitive (snapshot [binding "index.constant"])
        "algebra.exec.index_constant" "primitive" [text]).isOk)
  for text in ["0", "1", "9223372036854775808", "18446744073709551615"] do
    test ("index-valid:" ++ text) ((Format.indexDecimal text).isOk)
  test "pure-local-owner" (!admits [] [root, localHelper (.indexConstant "1") [] [.index]])
  test "pure-math" (admits [] [root, localHelper (.indexConstant "1") [] [.index] "" [] .math])
  test "pure-site" (!admits [] [root, localHelper .indexEqual [.index, .index] [.boolean] "site" [] .math])
  let mixed : Definition := .function ⟨"main", .protocol, .publicDef,
    [.index, .index], [], some ⟨["P", "V"], [["P"], ["V"]], []⟩, [], none,
    .block [.instruction .indexEqual [0, 1] [.boolean] [] ""] (.ret [])⟩
  test "unused-mixed-index-requirement" (!admits [] [mixed])
  let publicConstant : Definition := .function ⟨"main", .protocol, .publicDef,
    [], [.index], some ⟨["P", "V"], [], [["P", "V"]]⟩, [], none,
    .block [.instruction (.indexConstant "18446744073709551615") [] [.index] [] ""] (.ret [0])⟩
  test "public-pure-constant" (admits [] [publicConstant])
  let max := indexLimit - 1
  test "constant-max" (scalarIndex (.indexConstant max) .nil == some max)
  test "add-max-zero" (scalarIndex .indexAdd (.cons max (.cons 0 .nil)) == some max)
  test "add-boundary" (scalarIndex .indexAdd (.cons (max - 1) (.cons 1 .nil)) == some max)
  test "add-overflow" (stopped (Primitive.evaluate (F := F) (G := F) .indexAdd (.cons max (.cons 1 .nil))) .refused)
  test "mul-zero" (scalarIndex .indexMul (.cons 0 (.cons max .nil)) == some 0)
  test "mul-max-one" (scalarIndex .indexMul (.cons max (.cons 1 .nil)) == some max)
  test "mul-overflow" (stopped (Primitive.evaluate (F := F) (G := F) .indexMul (.cons max (.cons 2 .nil))) .refused)
  test "underflow" (stopped (Primitive.evaluate (F := F) (G := F) .indexSub (.cons 0 (.cons 1 .nil))) .refused)
  test "div-max" (scalarIndex .indexDiv (.cons max (.cons 8 .nil)) == some 2305843009213693951)
  test "mod-max" (scalarIndex .indexMod (.cons max (.cons 8 .nil)) == some 7)
  for xs in [[], [1], [1, 2, 3]] do
    test "split-invalid" (stopped (Primitive.evaluate (F := F) (G := F)
      (.vectorSplit scalarDomain) (.cons xs .nil)) .refused)
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"primitive failures: {errors.reverse}")
  IO.println s!"structured-primitives: {← count.get} controls passed"

#eval run
end Tests.StructuredPrimitives
