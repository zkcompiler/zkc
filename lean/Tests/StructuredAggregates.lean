import ZkcTools.StructuredSource.OpenEvaluation
import Zkc.Construction.DomainPublicBinding

/-! Independent aggregate formation and execution controls. These snapshots are
synthetic reader inputs, not claims about the native compiler's output. -/
namespace Tests.StructuredAggregates
open Lean Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource

private def field : Ty := .field scalarDomain
private def fields : ProductFields := .cons .boolean (.cons field .nil)
private def query : Ty := .product "[\"query\",\"bls12-381.fr\"]" "value" fields
private def queries : Ty := .sequence query
private def arr (values : List Json) : Json := .arr values.toArray
private def product (active : Bool) (value : Nat) : Json :=
  arr [.str "product", .str "[\"query\",\"bls12-381.fr\"]", .str "value",
    arr [arr [.str "bool", .bool active], arr [.str "field", .str scalarDomain, .str (toString value)]]]
private def sequence (values : List Json) : Json := arr [.str "sequence", wireType query, arr values]

private def make : Definition := .function ⟨"make", .math, .privateDef,
  [.boolean, field], [query], none, [], none,
  .block [.instruction (.makeProduct "value") [0, 1] [query] [] ""] (.ret [0])⟩
private def step : Definition := .function ⟨"step", .math, .privateDef,
  [.boolean, query, queries], [.boolean], none, [], none,
  .block [.instruction (.getProduct 0) [1] [.boolean] [] "",
    .instruction (.getProduct 1) [2] [field] [] "",
    .instruction .booleanAnd [2, 1] [.boolean] [] ""] (.ret [0])⟩
private def main : Definition := .function ⟨"main", .protocol, .publicDef,
  [queries], [.boolean], some ⟨["P"], [["P"]], [["P"]]⟩, [], some (.protocol ⟨"test::Main", []⟩),
  .block [.instruction (.booleanConstant true) [] [.boolean] [] "",
    .instruction (.fold "queries" "step" "") [1, 0] [.boolean] [] ""] (.ret [0])⟩
private def snapshot : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main",
    [⟨"queries", [queries], [.elements 0], 0⟩], [], [], [make, step, main], [⟨"main", []⟩], blsRows, {}⟩
private def runClosed (values : List Json) : Except String Json := do
  evaluate (← check snapshot) (arr [sequence values])
private def changedStep (op : Descriptor) (result : Ty) (operandType : Ty := query) : Snapshot :=
  { snapshot with definitions := [make,
    .function ⟨"step", .math, .privateDef, [.boolean, operandType, queries], [.boolean],
      none, [], none, .block [.instruction op [1] [result] [] ""] (.ret [1])⟩, main] }
private def refuses {α : Type} (actual : Except String α) (code : String) : Bool :=
  match actual with | .error error => error == code | .ok _ => false
private def equals (actual : Except String Json) (expected : Json) : Bool :=
  match actual with | .ok value => value == expected | .error _ => false

-- Universal component round trip and exact nominal identity are type-indexed.
example {carriers : Carriers} (value : carriers.Value query) :
    fields.pack (fields.unpack value) = value := ProductFields.pack_unpack fields value
example {carriers : Carriers} (first second : carriers.Value query)
    (same : Zkc.Construction.Domain.Payload.ofValue query first =
      Zkc.Construction.Domain.Payload.ofValue query second) : first = second :=
  Zkc.Construction.Domain.Payload.ofValue_injective (ty := query) rfl same

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  test "unit admission" (check snapshot).isOk
  for (label, values, expected) in [
      ("empty", [], true), ("single", [product true 7], true),
      ("false first", [product false 9, product true 7], false),
      ("false last", [product true 7, product false 9], false),
      ("duplicates", [product true 7, product true 7], true)] do
    test label (equals (runClosed values) (arr [.str "returned", arr [arr [.str "bool", .bool expected]]]))
  let packedProtocol : Snapshot := { snapshot with domains := [], definitions := [
    .function ⟨"main", .protocol, .publicDef, [.boolean, field], [.boolean],
      some ⟨["P"], [["P"], ["P"]], [["P"]]⟩, [], some (.protocol ⟨"test::Main", []⟩),
      .block [.instruction (.makeProduct "value") [0, 1] [query] [] "",
        .instruction (.getProduct 0) [0] [.boolean] [] ""] (.ret [0])⟩] }
  test "protocol product admission" (check packedProtocol).isOk
  for active in [false, true] do
    test s!"protocol product round trip {active}" (equals
      (do
        evaluate (← check packedProtocol)
          (arr [arr [.str "bool", .bool active], arr [.str "field", .str scalarDomain, .str "7"]]))
      (arr [.str "returned", arr [arr [.str "bool", .bool active]]]))
  let hiddenProduct : Snapshot := { packedProtocol with definitions := [
    .function ⟨"main", .protocol, .publicDef, [.boolean, field], [.boolean],
      some ⟨["P", "V"], [["P"], ["P"]], [["V"]]⟩, [], some (.protocol ⟨"test::Main", []⟩),
      .block [.instruction (.makeProduct "value") [0, 1] [query] [] "",
        .instruction (.getProduct 0) [0] [.boolean] [] ""] (.ret [0])⟩] }
  test "protocol packing does not grant another role the component" (!(check hiddenProduct).isOk)
  test "missing component" (!(check (changedStep (.getProduct 2) field)).isOk)
  test "wrong component sort" (!(check (changedStep (.getProduct 0) field)).isOk)
  let different : Ty := .product "other" "value" fields
  test "same shape wrong nominal item" (!(check (changedStep (.getProduct 0) .boolean different)).isOk)
  test "wrong constructor" (!(check { snapshot with definitions := [
    .function ⟨"make", .math, .privateDef, [.boolean, field], [query], none, [], none,
      .block [.instruction (.makeProduct "other") [0, 1] [query] [] ""] (.ret [0])⟩, step, main] }).isOk)
  test "dormant nested service" (refuses (snapshot.catalogue.checkType admittedCatalogue
    (.product "service" "value" (.cons (.sequence (.service "random.bls12-381.fr/0")) .nil)))
    "structured-aggregate-service")
  test "dormant unknown field" (!(snapshot.catalogue.checkType admittedCatalogue
    (.sequence (.product "unknown" "value" (.cons (.field "missing") .nil)))).isOk)
  test "exact type round trip" (Structured.Format.type (wireType queries) == .ok queries)
  test "bounded nesting" (!(Structured.Format.type
    (List.range 66 |>.foldl (fun type _ => arr [.str "sequence", type]) (wireType field))).isOk)
  test "wrong input identity" (refuses (input query
    (arr [.str "product", .str "other", .str "value", arr []])) "structured-input-domain")
  test "wrong input constructor" (refuses (input query
    (arr [.str "product", .str "[\"query\",\"bls12-381.fr\"]", .str "other", arr []]))
    "structured-input-domain")
  test "short product input" (refuses (input query
    (arr [.str "product", .str "[\"query\",\"bls12-381.fr\"]", .str "value", arr []]))
    "structured-input-count")
  test "noncanonical nested field" (refuses (input query (product true scalarModulus))
    "structured-input-field-canonical")
  test "open typed product round trip" (match wireInput query (arr [.bool false, .str "7"]) with
    | .ok value => wireOutput query value == arr [.bool false, .str "7"] | _ => false)
  let encoded := product false 13
  test "closed typed product round trip" (match input query encoded with
    | .ok value => equals (output query value) encoded | _ => false)
  test "capacity descends into product" (match (Bounds.checkValue
    (.product [.sequence (List.replicate 4097 .atom)])).run {} with
      | .error .value => true | _ => false)
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"aggregate failures: {errors.reverse}")
  IO.println s!"structured-aggregates: {← count.get} controls passed"

#eval run
end Tests.StructuredAggregates
