import ZkcTools.StructuredSource.Evaluation

/-! General finite realization admission is independent of immediate return.
These synthetic sources exercise callback closure and ordinary bound discharge.
Actual exported table formula laws are separate source-bound consumers. -/
namespace Tests.StructuredComputations
open Lean Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource

def vector : Ty := .vector scalarDomain
def field : Ty := .field scalarDomain

def step : Definition := .function ⟨"step", .math, .privateDef,
  [.boolean, .index, vector], [.boolean], none, [⟨1, 2, 0⟩], none,
  .block [.instruction (.boundedAt scalarDomain) [2, 1] [field] [] ""] (.ret [1])⟩
def predicate : Definition := .function ⟨"predicate", .math, .privateDef,
  [.index, vector], [.boolean], none, [⟨0, 1, 0⟩], none,
  .block [.instruction (.boundedAt scalarDomain) [1, 0] [field] [] "",
    .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])⟩
def calculation : Definition := .function ⟨"calculation", .math, .privateDef,
  [vector], [.boolean], none, [], none,
  .block [.instruction (.booleanConstant true) [] [.boolean] [] "",
    .instruction (.fold "coordinates" "step" "predicate") [1, 0] [.boolean] [] ""] (.ret [0])⟩
def main : Definition := .function ⟨"main", .protocol, .publicDef,
  [vector], [.boolean], some ⟨["P"], [["P"]], [["P"]]⟩, [], some (.protocol ⟨"test::Main", []⟩),
  .block [.instruction (.call "calculation") [0] [.boolean] [] ""] (.ret [0])⟩
def realization : RealizationDeclaration := ⟨"realized", [vector], [.boolean], "calculation"⟩

def snapshot : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main",
    [⟨"coordinates", [vector], [.indices 0 0], 0⟩], [], [], [main, calculation, predicate, step, .realization realization],
    [⟨"main", []⟩], blsRows, {}⟩

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let .ok program := check snapshot | throw (IO.userError "finite realization refused")
  let definitions := program.payload.definitions
  test "whole retained realization admitted"
    (program.snapshot.definitions.map Definition.name == snapshot.definitions.map Definition.name)
  test "complete step and predicate closure"
    ((computationHelpers definitions).map Helper.name == ["calculation", "step", "predicate"])
  test "finite root outside immediate-return fragment"
    (!(preparationHelpers .realization definitions).contains realization.helperSpec)
  test "finite root outside scalar-map fragment"
    (!(preparationHelpers .map definitions).contains realization.helperSpec)
  let missing := definitions.filter (fun definition => definition.name != "predicate")
  test "dormant predicate belongs to closure"
    (!(computationHelpers missing).contains realization.helperSpec)
  let .function stepFunction := step | throw (IO.userError "step shape")
  let .function predicateFunction := predicate | throw (IO.userError "predicate shape")
  let replace (name : String) (replacement : Definition) : Snapshot := { snapshot with
    definitions := snapshot.definitions.map fun definition =>
      if definition.name == name then replacement else definition }
  test "undischarged step read refused"
    (!(check (replace "step" (.function {stepFunction with preconditions := []}))).isOk)
  test "undischarged predicate read refused"
    (!(check (replace "predicate" (.function {predicateFunction with preconditions := []}))).isOk)
  test "wrong predicate ABI refused"
    (!(check (replace "predicate" (.function {predicateFunction with inputs := [.index, field]}))).isOk)
  test "same-name changed kind refused"
    (!(check (replace "predicate" (.function {predicateFunction with kind := .local}))).isOk)
  test "realization with external premise refused" (!(check { snapshot with definitions :=
    snapshot.definitions ++ [.realization ⟨"premised", stepFunction.inputs, stepFunction.outputs, "step"⟩] }).isOk)
  for values in [[], [0], [7, 7], [3, 9, 2]] do
    let inputs := Json.arr #[Json.arr #[.str "vector", .str scalarDomain,
      .arr (values.map (fun value : Nat => Json.str (toString value))).toArray]]
    test s!"finite evaluation length {values.length}" (match evaluate program inputs with
      | .ok result => result == Json.arr #[.str "returned", .arr #[.arr #[.str "bool", .bool true]]]
      | .error _ => false)
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"finite computation failures: {errors.reverse}")
  IO.println s!"structured-computations: {← count.get} controls passed"

#eval run
end Tests.StructuredComputations
