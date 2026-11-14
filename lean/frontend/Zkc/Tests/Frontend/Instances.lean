import Zkc.Tests.Frontend.Names
import Zkc.Tests.Frontend.InstanceCases

/-!
# The check of instances, without the reference

The programs of `InstanceCases` over the library of `NameCases`, and the matcher of SP6 on its
own: parameter types with unknowns against closed types.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Instances
open Zkc.Frontend.Static
open Zkc.Frontend.Static.Infer (Problem startProblem matchType retry finish)
open Zkc.Frontend.Syntax

/-- Runs a computation of the check of instances on a state, for its value. -/
def runCheck {α : Type} (state : Compile.State) (action : CompileM α) : Option α :=
  match (action.run { vocabulary := Zkc.Frontend.vocabulary } state).1 with
  | .ok value => some value
  | .error _ => none

/-- The descriptions of the instances of a check, with their contents. -/
def describedInstances (check : InstanceCheck) : Array (String × String) := Id.run do
  let mut result := #[]
  for entry in check.state.table.entries do
    let description := (runCheck check.state
      (describeInstance entry.key.declaration entry.key.arguments)).getD "?"
    let content := match entry.state with
      | .done (.data content) => renderContent check.state content
      | .done _ => "a signature"
      | .failed => "failed"
      | .skipped => "skipped"
      | .inProgress => "in progress"
      | .waiting reason => s!"waiting for {reason}"
      | .exhausted exhaustion => s!"not checked: {exhaustion.describe}"
    result := result.push (description, content)
  return result

/-- Checks the assertions `// content`, `// chain`, `// default`, `// no default` and
`// reached`. -/
def checkInstanceAssertions (label : String) (check : InstanceCheck) (source : String) :
    TestM Unit := do
  let instances := describedInstances check
  let program := check.names.program
  for line in source.splitOn "\n" do
    if line.startsWith "// content " then
      let some (description, expected) := splitFirst (String.ofList (line.toList.drop 11)) " holds "
        | failure s!"{label}: unreadable assertion `{line}`"
      match instances.find? (·.1 == description) with
      | some (_, found) =>
        expectTrue (found == expected) s!"{label}: `{description}` holds `{found}`, expected `{expected}`"
      | none =>
        failure s!"{label}: no instance `{description}`; the instances are {instances.map (·.1)}"
    else if line.startsWith "// chain " then
      let expected := String.ofList (line.toList.drop 9)
      match check.refusals[0]? with
      | some first =>
        let found := (first.chain[0]?.map (·.description)).getD "none"
        expectTrue (found == expected) s!"{label}: the first frame is `{found}`, expected `{expected}`"
      | none => failure s!"{label}: no refusal has a chain"
    else if line.startsWith "// default " then
      let some (name, expected) := splitFirst (String.ofList (line.toList.drop 11)) " = "
        | failure s!"{label}: unreadable assertion `{line}`"
      match check.state.defaults.find? (program.nameOf ·.declaration == name) with
      | some entry =>
        let found := s!"{entry.count}, {entry.first.getD "none"}"
        expectTrue (found == expected) s!"{label}: the default instances of `{name}` are `{found}`, expected `{expected}`"
      | none => failure s!"{label}: `{name}` has no report of default instances"
    else if line.startsWith "// no default " then
      let name := String.ofList (line.toList.drop 14)
      match check.state.defaults.find? (program.nameOf ·.declaration == name) with
      | some entry => expectTrue entry.none?.isSome s!"{label}: `{name}` has default instances"
      | none => failure s!"{label}: `{name}` has no report of default instances"
    else if line.startsWith "// reached " then
      let name := String.ofList (line.toList.drop 11)
      expectTrue (check.state.defaults.all (program.nameOf ·.declaration != name))
        s!"{label}: `{name}` has a report of default instances although a root reaches it"

def checkInstanceBlock (block : Block) : TestM Unit := do
  let names := (List.range block.files.size).toArray.map fun index => s!"{block.id}.{index}"
  let inputs := (block.files.zip names).map fun (text, name) =>
    ({ name, parsed := parseString name text } : SourceInput)
  let nameCheck := Id.run (checkNames inputs (memoryLoader nameLibrary))
  if let some first := nameCheck.refusals[0]? then
    failure s!"{block.id}: the names do not resolve; {first.span.file}: {first.render}"
    return
  let check := checkInstances nameCheck names
  let words := (block.expect.splitOn " ").filter (· != "")
  match words with
  | ["accept"] =>
    match check.refusals[0]? with
    | none => pass
    | some first => failure s!"{block.id}: expected to be accepted; {first.span.file}: {first.render}"
  | "refuse" :: rule :: place :: rest =>
    let fileName := match rest with
      | ["in", which] => if which.all Char.isDigit then s!"{block.id}.{which}" else which
      | _ => names[0]!
    match check.refusals[0]? with
    | some first =>
      let position := match place.splitOn ":" with
        | [_] => s!"{first.span.startLine}"
        | _ => s!"{first.span.startLine}:{first.span.startColumn}"
      expectTrue (first.rule == rule && first.span.file == fileName && position == place)
        s!"{block.id}: expected a refusal by {rule} at {place} in {fileName}; {first.span.file}: {first.render}"
    | none => failure s!"{block.id}: expected a refusal by {rule} at {place}; the instances are formed"
  | _ => failure s!"{block.id}: unreadable expectation `{block.expect}`"
  for text in block.files do checkInstanceAssertions block.id check text

/-! ## The matcher -/

/-- Matches parameters of a function of a program against closed types, and prints the values
found (`n = 2, …`), or the first refusal. `arguments` builds each closed type in the state. -/
def matchCase (source : String) (callee : String)
    (arguments : Array (Nat × CompileM ClosedType)) : String := Id.run do
  let input : SourceInput := { name := "case", parsed := parseString "case" source }
  let nameCheck := Id.run (checkNames #[input] (memoryLoader nameLibrary))
  if let some first := nameCheck.refusals[0]? then return s!"names: {first.render}"
  let state := Instances.withIndexes nameCheck.session.state
  let program := nameCheck.program
  let action : CompileM String := do
    let some id := (List.range program.declarations.size).find? fun id =>
        program.nameOf id == callee && (program.declarations[id]!.kind == .function)
      | return "no callee"
    let found ← declaration id
    let some { content := .function head _, .. } := (← getModules).lowered? id | return "not a function"
    let mut problem ← startProblem id {}
    let context : Static.Infer.Context := .context found.file []
    for (index, actual) in arguments do
      let some parameter := head.parameters[index]? | return "no parameter"
      problem ← matchType problem context parameter.type (← actual)
    problem ← retry problem
    let values ← finish problem default
    let shown ← (deployedParameters program found).mapM fun (reference, parameter) => do
      return s!"{parameter.name.text} = {← renderValueM (values.getD reference default)}"
    let conflicts ← problem.conflicts.mapM fun (reference, a, b) => do
      let name := ((program.scopes[reference.scope]?).bind (·.parameters[reference.index]?)).map (·.name.text)
      return s!"; {name.getD "?"} found as {← renderValueM a} and {← renderValueM b}"
    return ", ".intercalate shown.toList ++ String.join conflicts.toList
  match action.run { vocabulary := Zkc.Frontend.vocabulary } state with
  | (.ok text, _) => text
  | (.error _, final) => match final.log.entries[0]? with
    | some refusal => s!"refuse {refusal.rule} {refusal.message.render Renderer.plain}"
    | none => "failed without a refusal"

def bytes (size : Nat) : CompileM ClosedType := pure (.seq (.index 256) (some size))

/-- An instance of a declaration of the program by its name, at values. -/
def instanceOf (name : String) (values : Array StaticValue) : CompileM InstanceId := do
  let program ← Static.program
  let some id := (List.range program.declarations.size).find? (program.nameOf · == name)
    | throw (.waiting "no declaration")
  instantiate id values { description := name, span := default }

def matcherSuite : TestM Unit := do
  let check (label expected found : String) : TestM Unit :=
    expectTrue (found == expected) s!"matcher, {label}: `{found}`, expected `{expected}`"
  check "a power" "k = 2"
    (matchCase "module t\ndef half<k: nat>(xs: [byte; 2^(k + 1)]) -> [byte; 2^k]: xs[0..2^k]\n"
      "half" #[(0, bytes 8)])
  check "an alias stands for its definition" "v = 3"
    (matchCase "module t\ntype Table<v: nat> = [byte; 2^v]\ndef sums<v: nat>(table: Table<v + 1>) -> nat: 0\n"
      "sums" #[(0, bytes 16)])
  check "a sum set aside, then solved" "a = 2, b = 3"
    (matchCase "module t\ndef two<a: nat, b: nat>(x: [byte; a + b], y: [byte; a]) -> nat: 0\n"
      "two" #[(0, bytes 5), (1, bytes 2)])
  check "a product is not solved" "refuse SP6 cannot infer `a` of `grid`; write `grid<a = …>`"
    (matchCase "module t\ndef grid<a: nat, b: nat>(x: [byte; a * b]) -> nat: 0\n"
      "grid" #[(0, bytes 6)])
  check "a type parameter" "T = bool, n = 3"
    (matchCase "module t\ndef first<T, n: nat>(xs: [T; n]) -> T: xs[0]\n"
      "first" #[(0, pure (.seq .bool (some 3)))])
  check "nonzero against a type" "F = bls12-381.fr"
    (matchCase "module t\ndef inverse<F>(x: nonzero<F>) -> F: x\n"
      "inverse" #[(0, pure (.nominal "bls12-381.fr" #[]))])
  check "a difference" "n = 5"
    (matchCase "module t\ndef drop<n: nat>(x: index<n - 2>) -> nat: 0\n"
      "drop" #[(0, pure (.index 3))])
  check "a value found twice" "n = 2; n found as 2 and 3"
    (matchCase "module t\ndef same<n: nat>(x: [byte; n], y: [byte; n]) -> nat: 0\n"
      "same" #[(0, bytes 2), (1, bytes 3)])
  check "a module, argument by argument" "T = bool, k = 3"
    (matchCase ("module t\ninterface Shape:\n    nat Size\nmodule grid<T, n: nat>: Shape:\n" ++
        "    nat Size = n\nstruct Holder<M: Shape>:\n    size: index<M::Size>\n" ++
        "def use_grid<T, k: nat>(h: Holder<grid<T, 2^k>>) -> nat: 0\n")
      "use_grid" #[(0, do
        let module ← instanceOf "grid" #[.type .bool, .natural 8]
        let holder ← instanceOf "Holder" #[.«module» module]
        pure (.record holder))])
  check "a record, argument by argument" "n = 4"
    (matchCase "module t\nstruct Row<n: nat>:\n    cells: [byte; n]\ndef width<n: nat>(r: Row<n>) -> nat: n\n"
      "width" #[(0, do pure (.record (← instanceOf "Row" #[.natural 4])))])

def instanceCaseSuite : TestM Unit := do
  let blocks := readBlocks instanceCases
  for block in blocks do checkInstanceBlock block
  note s!"{blocks.size} programs for the check of instances"
  matcherSuite

end Zkc.Tests.Frontend
