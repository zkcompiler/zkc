import Zkc.Source.Structured.Admission
import Zkc.Source.Structured.Component
import Zkc.Source.KernelRfl
import Mathlib.Data.ZMod.Basic

/-! Admission and semantic controls for decoded declarations. They preserve the
existing primitive interpreter, checked arithmetic and optional-input meaning. -/

open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredFoundationPrimitives

private def arr (values : List Json) : Json := .arr values.toArray
private def strs (values : List String) : Json := arr (values.map Json.str)
private def app (name : String) (args : List Json := []) : Json :=
  arr [.str "apply", .str name, arr args]
private def field (name : String) : Json := app "field" [strs ["domain", "Field", name]]
private def wire (contract : String) (args inputs outputs : List Json) : Json :=
  arr [.str "binding", .str "primitive", .str contract, arr args, .str "", arr inputs, arr outputs]
private def snapshot (bindings : List Binding) (catalogue : Catalogue := admittedCatalogue) : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], bindings,
    [], [], catalogue, {}⟩
private def refusal {α : Type} (value : Except String α) (code : String) : Bool :=
  match value with | .error actual => actual == code | _ => false
private def decoded (json : Json) : IO Binding :=
  match Format.binding json with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private abbrev F := ZMod 97

/-- A stopping operation remains reached even when no returned value is used. -/
private def discardedDivision : Region dialect [.index, .index] [] :=
  .letOp (.exec .indexDiv) (.cons .here (.cons (.there .here) .nil)) .nil (.ret .nil)

example : discardedDivision.denote (meaning F F [])
    (Values.cons 8 (.cons 0 .nil)).get = .halt .refused := by kernel_rfl

example : discardedDivision.component (meaning F F [])
    (Evaluation.componentOperation SiteObservations.closed ⟨[], []⟩)
    (Values.cons (some 8) (.cons none .nil)).get = .halt .incomplete := by kernel_rfl

example : Primitive.evaluate (F := F) (G := F) .indexAdd
    (.cons 18446744073709551615 (.cons 1 .nil)) = .stopped .refused := by kernel_rfl

example : Primitive.evaluate (F := F) (G := F) .indexSub
    (.cons 1 (.cons 2 .nil)) = .stopped .refused := by kernel_rfl

example : Primitive.evaluate (F := F) (G := F) (.vectorSplit "f")
    (.cons [1, 7, 2, 9] .nil) = .returned (.cons [1, 7] (.cons [2, 9] .nil)) := rfl

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let add ← decoded (wire "index.add" [] [app "index", app "index"] [app "index"])
  test "retained-complete-binding" (add.schema == some ⟨[], [.index, .index], [.index]⟩)
  test "decoded-addition-meaning" (match resolvePrimitive (snapshot [add]) "exec.apply" add.name [] with
    | .ok (.exec .indexAdd) => true | _ => false)
  let sub ← decoded (wire "index.sub" [] [app "index", app "index"] [app "index"])
  test "same-ports-distinct-meaning" (match resolvePrimitive (snapshot [sub]) "exec.apply" sub.name [] with
    | .ok (.exec .indexSub) => true | _ => false)
  test "forged-internal-signature" (refusal
    ({add with schema := some ⟨[], [.index, .index], [.boolean]⟩}.resolveRoot admittedCatalogue)
    "structured-binding-signature")
  test "forged-internal-kinded-arguments" (refusal
    ({add with schema := some ⟨[.natural 1], [.index, .index], [.index]⟩}.resolveRoot admittedCatalogue)
    "structured-binding")
  let constant ← decoded (wire "index.constant" [] [] [app "index"])
  test "decoded-u64-constant" (match resolvePrimitive (snapshot [constant]) "exec.apply" constant.name
      (← match Format.primitiveParameters (arr [strs ["natural", "18446744073709551615"]]) with
        | .ok value => pure value | .error error => throw (IO.userError error)) with
    | .ok (.exec (.indexConstant 18446744073709551615)) => true | _ => false)
  test "constant-needs-parameter" (refusal
    (resolvePrimitive (snapshot [constant]) "exec.apply" constant.name []) "structured-primitive-parameters")
  test "constant-needs-one-parameter" (refusal
    (resolvePrimitive (snapshot [constant]) "exec.apply" constant.name ["0", "1"])
    "structured-primitive-parameters")
  test "none-schema-refuses-natural" (refusal
    (resolvePrimitive (snapshot [add]) "exec.apply" add.name ["1"]) "structured-primitive-parameters")
  let extension := "koala-bear.ext8-binomial3"
  let base := "koala-bear"
  let embed ← decoded (wire "field.embed" [strs ["domain", "Field", extension]]
    [field base] [field extension])
  test "embedding-associated-base-signature" ((embed.resolveRoot admittedCatalogue).isOk)
  test "standalone-complete-binding-admission" ((Format.bindingIn admittedCatalogue
    (wire "field.embed" [strs ["domain", "Field", extension]] [field base] [field extension])).isOk)
  test "embedding-existing-meaning" (match resolvePrimitive (snapshot [embed]) "exec.apply" embed.name [] with
    | .ok (.fieldEmbed actualExtension actualBase) => actualExtension == extension && actualBase == base
    | _ => false)
  let wrongBase ← decoded (wire "field.embed" [strs ["domain", "Field", extension]]
    [field scalarDomain] [field extension])
  test "embedding-producer-base-is-not-authority" (refusal (wrongBase.resolveRoot admittedCatalogue)
    "structured-binding-signature")
  test "standalone-forged-base-refusal" (refusal (Format.bindingIn admittedCatalogue
    (wire "field.embed" [strs ["domain", "Field", extension]] [field scalarDomain] [field extension]))
    "structured-binding-signature")
  let forged : Catalogue := { admittedCatalogue with nominals := admittedCatalogue.nominals.map fun row =>
    if row.identity == extension then {row with members := [("BaseField", scalarDomain)]} else row }
  test "embedding-characteristic-check" (refusal (embed.resolveRoot forged) "structured-domain-modulus")
  let nonExtension ← decoded (wire "field.embed" [strs ["domain", "Field", base]]
    [field base] [field base])
  test "field-membership-is-not-embedding" (refusal (nonExtension.resolveRoot admittedCatalogue)
    "structured-domain-capability")
  let sum ← decoded (wire "vector.sum" [strs ["domain", "Field", base]]
    [app "vector" [strs ["domain", "Field", base]]] [field base])
  test "domain-projection-retained" (sum.arguments == [base] && sum.schema ==
    some ⟨[.domain "Field" base], [.vector base], [.field base]⟩)
  test "unknown-domain" (refusal (sum.resolveRoot blsRows) "structured-domain-unknown")
  let ringOnly : Catalogue := ⟨[⟨"f", .field, [], ["CommRing"], some 5⟩], [], []⟩
  let equality ← decoded (wire "vector.equal" [strs ["domain", "Field", "f"]]
    [app "vector" [strs ["domain", "Field", "f"]], app "vector" [strs ["domain", "Field", "f"]]]
    [app "bool"])
  test "vector-equality-existing-ring-requirement" ((equality.resolveRoot ringOnly).isOk)
  let fieldOnly : Catalogue := ⟨[⟨"f", .field, [], ["Field"], some 5⟩], [], []⟩
  test "missing-ring-capability" (refusal (equality.resolveRoot fieldOnly) "structured-domain-capability")
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError (String.intercalate "\n" errors.reverse))
  IO.println s!"Structured foundation primitives: {← count.get} controls passed"

#eval run

end Tests.StructuredFoundationPrimitives
