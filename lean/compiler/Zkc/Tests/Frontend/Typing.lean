import Zkc.Core.Package
import Zkc.Tests.Frontend.Instances
import Zkc.Tests.Frontend.TypingCases

/-!
# The typing of bodies, without the reference

The programs of `TypingCases` over the library of `NameCases`: names, instances, the typing of
bodies, and the packages of the core emitted for their roots, admitted by its `elaborate` and its
check of facts.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- The JSON text of every package a check emitted. -/
def packageTexts (check : TypingCheck) : Array String :=
  check.packages.filterMap fun report => match report.outcome with
    | .admitted package | .refused _ package | .unjustified _ package =>
      some (Zkc.Core.Raw.printPackage package).render
    | _ => none

/-- Checks the packages of a check: none refused by the core, none not emitted, and every
function passes the core's check of facts. -/
def checkPackages (label : String) (check : TypingCheck) : TestM Unit := do
  for report in check.packages do
    match report.outcome with
    | .refused reason _ => failure s!"{label}: the core refuses the package of {report.description}: {reason}"
    | .unjustified functions _ =>
      failure s!"{label}: the package of {report.description} does not pass the check of facts: {"; ".intercalate functions.toList}"
    | .defect message => failure s!"{label}: the package of {report.description} is not emitted: {message}"
    | .exhausted exhaustion =>
      failure s!"{label}: the package of {report.description} is not checked: {exhaustion.describe}"
    | _ => pure ()

/-- The functions of the packages that the core elaborated, and those among them that do not
pass the check of facts. -/
def checkedFunctions (check : TypingCheck) : Nat × Nat :=
  check.packages.foldl (init := (0, 0)) fun (checked, failing) report =>
    match report.outcome with
    | .admitted package => (checked + package.functions.length, failing)
    | .unjustified functions package => (checked + package.functions.length, failing + functions.size)
    | _ => (checked, failing)

/-- The packages of protocol roots that the core admitted, with the check of facts of every
protocol and function in them, and the protocols those packages hold. -/
def checkedProtocols (check : TypingCheck) : Nat × Nat :=
  check.packages.foldl (init := (0, 0)) fun (roots, protocols) report =>
    match report.outcome, check.state.results.body? report.root with
    | .admitted package, some (.protocol _) => (roots + 1, protocols + package.protocols.length)
    | _, _ => (roots, protocols)

/-- Checks the assertions `// uses`, `// not uses`, `// applies`, `// obligations`, `// waits` and
`// says`. -/
def checkTypingAssertions (label : String) (check : TypingCheck) (source : String) : TestM Unit := do
  let texts := packageTexts check
  let waits := check.packages.filterMap fun report => match report.outcome with
    | .waiting reason => some reason
    | _ => none
  for line in source.splitOn "\n" do
    if line.startsWith "// uses " then
      let name := String.ofList (line.toList.drop 8)
      expectTrue (texts.any fun text => (text.splitOn s!"\"{name}\"").length > 1)
        s!"{label}: no package applies `{name}`"
    else if line.startsWith "// not uses " then
      let name := String.ofList (line.toList.drop 12)
      expectTrue (texts.all fun text => (text.splitOn s!"\"{name}\"").length == 1)
        s!"{label}: a package applies `{name}`"
    else if line.startsWith "// applies " then
      match (String.ofList (line.toList.drop 11)).splitOn " " with
      | [name, count] =>
        let found := texts.foldl (init := 0) fun total text => total + ((text.splitOn s!"\"{name}\"").length - 1)
        expectTrue (some found == count.toNat?)
          s!"{label}: the packages apply `{name}` {found} times; {count} are expected"
      | _ => failure s!"{label}: unreadable assertion `{line}`"
    else if line.startsWith "// obligations " then
      let count := (String.ofList (line.toList.drop 15)).toNat?
      let found := check.state.results.obligations.size
      expectTrue (some found == count) s!"{label}: the laws typed leave {found} obligations; {line.drop 15} are expected"
    else if line.startsWith "// says " then
      let text := String.ofList (line.toList.drop 8)
      let messages := check.refusals.map (·.render)
      expectTrue (messages.any fun found => (found.splitOn text).length > 1)
        s!"{label}: no refusal says `{text}`; the refusals are {messages}"
    else if line.startsWith "// waits " then
      let reason := String.ofList (line.toList.drop 9)
      expectTrue (waits.any fun found => (found.splitOn reason).length > 1)
        s!"{label}: no root waits for `{reason}`; the roots wait for {waits}"

/-- Names, instances and typing of the files of a block. -/
def typeBlock (block : Block) : Except String (TypingCheck × Array String) := do
  let names := (List.range block.files.size).toArray.map fun index => s!"{block.id}.{index}"
  let inputs := (block.files.zip names).map fun (text, name) =>
    ({ name, parsed := parseString name text } : SourceInput)
  let nameCheck := Id.run (checkNames inputs (memoryLoader nameLibrary))
  if let some first := nameCheck.refusals[0]? then
    throw s!"the names do not resolve; {first.span.file}: {first.render}"
  let instances := checkInstances nameCheck names
  return (checkTyping instances names, names)

def checkTypingBlock (block : Block) : TestM Unit := do
  let (check, names) ← match typeBlock block with
    | .ok result => pure result
    | .error message => do failure s!"{block.id}: {message}"; return
  let words := (block.expect.splitOn " ").filter (· != "")
  match words with
  | ["accept"] =>
    match check.refusals[0]? with
    | some first => failure s!"{block.id}: expected to be accepted; {first.span.file}: {first.render}"
    | none =>
      let waiting := check.packages.filter fun report => report.outcome matches .waiting _
      if waiting.isEmpty then pass
      for report in waiting do
        if let .waiting reason := report.outcome then
          failure s!"{block.id}: expected to be admitted; {report.description} waits for {reason}"
  | ["wait"] =>
    match check.refusals[0]? with
    | some first => failure s!"{block.id}: expected to wait; {first.span.file}: {first.render}"
    | none =>
      expectTrue (check.packages.any fun report => report.outcome matches .waiting _)
        s!"{block.id}: expected a root to wait"
  | "refuse" :: rule :: place :: _ =>
    match check.refusals[0]? with
    | some first =>
      let position := match place.splitOn ":" with
        | [_] => s!"{first.span.startLine}"
        | _ => s!"{first.span.startLine}:{first.span.startColumn}"
      expectTrue (first.rule == rule && first.span.file == names[0]! && position == place)
        s!"{block.id}: expected a refusal by {rule} at {place}; {first.span.file}: {first.render}"
    | none => failure s!"{block.id}: expected a refusal by {rule} at {place}; the bodies type"
  | _ => failure s!"{block.id}: unreadable expectation `{block.expect}`"
  checkPackages block.id check
  for text in block.files do checkTypingAssertions block.id check text

def typingCaseSuite : TestM Unit := do
  let blocks := readBlocks typingCases
  for block in blocks do checkTypingBlock block
  note s!"{blocks.size} programs for the typing of bodies"

end Zkc.Tests.Frontend
