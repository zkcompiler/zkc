import ZkcTools.StructuredSource.Evaluation
import Zkc.Source.Structured.CollectLaws

/-! Synthetic controls of the actual domain/callback contract. Native source
export and imported protocol equations are exercised separately. -/
namespace Tests.StructuredCollections
open Lean Zkc.Source Zkc.Source.Structured

def field : Ty := .field scalarDomain
def vector : Ty := .vector scalarDomain
def digest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')

def localFunction (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .local, .privateDef, inputs, outputs, none, [], some (.local name []), body⟩

def source (domain : Domain) (items : List Ty) (collection : Collection) (body : Block)
    (captures : List Ty := []) (predicate : Option Block := none) : Snapshot := Id.run do
  let args := domain.inputs ++ captures
  let callback := items ++ args
  let output := [collection.type]
  let predicateName := if predicate.isSome then "predicate" else ""
  let definitions := [
    localFunction "body" callback [collection.element] body,
    .collect ⟨"collect", .privateDef, args, output, domain.name, "body", predicateName⟩,
    localFunction "work" args output
      (.block [.instruction (.apply "collect") (List.range args.length) output [] "collect"] (.ret [0])),
    .function ⟨"main", .protocol, .publicDef, args, output,
      some ⟨["P"], args.map (fun _ => ["P"]), [["P"]]⟩, [], some (.protocol ⟨"main", []⟩),
      .block [.instruction (.localCall "work" "P") (List.range args.length) output [] "work"] (.ret [0])⟩]
  let definitions := match predicate with
    | none => definitions
    | some predicate => localFunction "predicate" callback [.boolean] predicate :: definitions
  return ⟨digest, "main", [domain], [], [], definitions, [⟨"main", []⟩], blsRows⟩

def zipped : Domain := ⟨"rows", [vector, vector], [.elements 0, .elements 1, .zip [1, 0]], 0⟩
def product : Domain := { zipped with constructors := [.elements 0, .elements 1, .product [1, 0]] }
def first : Block := .block [] (.ret [0])
def second : Block := .block [] (.ret [1])
def aborting : Block := .block [] (.stop .abort "abort")
def rejected : Block := .block [] (.stop .reject "reject")
def enabled (value : Bool) : Block :=
  .block [.instruction (.booleanConstant value) [] [.boolean] [] "enabled"] (.ret [0])

def vectorValue (values : List Nat) : Json :=
  .arr #[.str "vector", .str scalarDomain, .arr (values.map fun n => Json.str (toString n)).toArray]
def indexValue (value : Nat) : Json := .arr #[.str "index", toJson value]
def sequenceValue (values : List Nat) : Json :=
  .arr #[.str "sequence", .arr #[.str "index"], .arr (values.map indexValue).toArray]
def booleanSequence (values : List Bool) : Json :=
  .arr #[.str "sequence", .arr #[.str "bool"],
    .arr (values.map fun value => Json.arr #[.str "bool", .bool value]).toArray]
def returned (value : Json) : Json := .arr #[.str "returned", .arr #[value]]
def stopped (reason : String) : Json := .arr #[.str "stopped", .str reason]

def evaluates (snapshot : Snapshot) (args : List Json) (expected : Json) : Bool :=
  match check snapshot >>= fun program => ZkcTools.StructuredSource.evaluate program (.arr args.toArray) with
  | .ok actual => actual == expected
  | .error _ => false

def refusal (snapshot : Snapshot) (code : String) : Bool :=
  match check snapshot with | .error actual => actual == code | _ => false

def replace (snapshot : Snapshot) (name : String) (replacement : Definition) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun definition =>
      if definition.name == name then replacement else definition }

private def run : IO Unit := do
  let count ← IO.mkRef 0
  let errors ← IO.mkRef ([] : List String)
  let test (label : String) (passed : Bool) : IO Unit := do
    count.modify (· + 1)
    unless passed do errors.modify (label :: ·)
  for (left, right) in [([], []), ([3], [7]), ([5, 2, 5], [11, 13, 17])] do
    let args := [vectorValue left, vectorValue right]
    test "zip returns left tuple component in source order"
      (evaluates (source zipped [field, field] (.vector scalarDomain) first) args (returned (vectorValue left)))
    test "zip returns right tuple component in source order"
      (evaluates (source zipped [field, field] (.vector scalarDomain) second) args (returned (vectorValue right)))
  for (left, right) in [([], [1]), ([1], []), ([1, 2], [3])] do
    test "ignored row still requires equal cardinality"
      (evaluates (source zipped [field, field] (.vector scalarDomain) first)
        [vectorValue left, vectorValue right] (stopped "refused"))
  for (left, right) in [([], [1, 2]), ([3, 5], []), ([3, 5], [7, 11, 13])] do
    test "product last factor varies fastest"
      (evaluates (source product [field, field] (.vector scalarDomain) second)
        [vectorValue left, vectorValue right]
        (returned (vectorValue (left.flatMap fun _ => right))))
    test "product preserves outer duplicates"
      (evaluates (source product [field, field] (.vector scalarDomain) first)
        [vectorValue left, vectorValue right]
        (returned (vectorValue (left.flatMap fun value => right.map fun _ => value))))
  let unused : Domain := { zipped with result := 2 }
  test "unused zip mismatch precedes returned first descriptor"
    (evaluates (source unused [field] (.vector scalarDomain) first)
      [vectorValue [], vectorValue [2]] (stopped "refused"))
  let single : Domain := ⟨"items", [vector], [.elements 0], 0⟩
  test "empty domain never calls stopping body"
    (evaluates (source single [field] (.vector scalarDomain) aborting) [vectorValue []]
      (returned (vectorValue [])))
  test "false predicate skips stopping body"
    (evaluates (source single [field] (.vector scalarDomain) aborting [] (some (enabled false)))
      [vectorValue [3, 5]] (returned (vectorValue [])))
  test "true predicate retains body stop"
    (evaluates (source single [field] (.vector scalarDomain) aborting [] (some (enabled true)))
      [vectorValue [3]] (stopped "abort"))
  test "predicate stop precedes body stop"
    (evaluates (source single [field] (.vector scalarDomain) aborting [] (some rejected))
      [vectorValue [3]] (stopped "reject"))
  let mixed : Domain := ⟨"mixed", [vector, .sequence .boolean],
    [.elements 0, .elements 1, .zip [1, 0]], 0⟩
  test "heterogeneous tuple filters in source order"
    (evaluates (source mixed [field, .boolean] (.vector scalarDomain) first [] (some second))
      [vectorValue [7, 3, 9], booleanSequence [true, false, true]] (returned (vectorValue [7, 9])))
  let range : Domain := ⟨"range", [.index, .index], [.range 0 1], 0⟩
  for (lo, hi) in [(0, 0), (3, 2), (4, 8)] do
    test "range collection preserves reversed and ordered cases"
      (evaluates (source range [.index] (.sequence .index) first) [indexValue lo, indexValue hi]
        (returned (sequenceValue (List.range' lo (hi - lo)))))
  let sample := source zipped [field, field] (.vector scalarDomain) first
  test "wrong body signature refused" (refusal (replace sample "body"
    (localFunction "body" [field] [field] first)) "structured-collect-body")
  test "missing dormant body refused" (refusal { sample with
      definitions := sample.definitions.filter (fun definition => definition.name != "body") } "structured-unknown-helper")
  let filtered := source zipped [field, field] (.vector scalarDomain) first [] (some (enabled false))
  test "wrong dormant predicate signature refused" (refusal (replace filtered "predicate"
    (localFunction "predicate" [field] [.boolean] (enabled false))) "structured-collect-predicate")
  for constructor in [DomainConstructor.zip [], .product [], .zip [2], .product [9]] do
    test "invalid domain references refused independently of callbacks"
      (!(check { sample with domains := [{ zipped with constructors := [.elements 0, constructor] }] }).isOk)
  let indices : Domain := { zipped with constructors := [.indices 0 0, .indices 1 0, .zip [1, 0]] }
  test "index provenance follows flattened tuple positions"
    (match indices.resolve with | .ok domain => domain.bounds == [(0, 0), (1, 1)] | _ => false)
  let huge := source product [field, field] (.vector scalarDomain) first
  test "product capacity refused before enumeration"
    (match check huge >>= fun program => ZkcTools.StructuredSource.evaluate program
        (.arr #[vectorValue (List.replicate 2048 1), vectorValue (List.replicate 2048 1)]) with
      | .error code => code == "structured-evaluation-work-limit"
      | _ => false)
  let failed ← errors.get
  unless failed.isEmpty do throw (IO.userError s!"collection controls failed: {failed.reverse}")
  IO.println s!"Structured collection controls passed ({← count.get})"

#eval run
end Tests.StructuredCollections
