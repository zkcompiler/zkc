import Zkc.Core.Program.Links
import Zkc.Tests.Frontend.PrintedFixtures
import Zkc.Frontend.Written.Package
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

/-- The source packages presented to core admission, including those it refused. -/
def emittedPackages (check : TypingCheck) : Array SourcePackage :=
  check.packages.filterMap fun report => match report.outcome with
    | .admitted checked => some checked.toSourcePackage
    | .refused source _ => some source
    | _ => none

def packageTexts (check : TypingCheck) : Array String :=
  (emittedPackages check).map fun source => (Written.package source).text

/-- An assertion names a loop instruction or an operation of a function or role. -/
private inductive FixtureOperation where
  | loop
  | localOp (test : (p : SourcePackage) → Zkc.Core.LocalRaw p.bindings.vocabulary → Bool)

private def resolveOperation (check : TypingCheck) (name : String) : Option FixtureOperation := do
  if name == "loop" then return .loop
  if let some expected := PrintedFixtures.ownedNames.find? (fun op => Typed.CoreOperation.ownedSpelling op == name) then
    return .localOp fun _ => fun | .owned op .. => op == expected | _ => false
  let standard : Option (Zkc.Vocabulary.RowKey → Bool) := do
    if let some field := Typing.StandardRow.fieldOp name then
      return fun | .field op .. => op == field | _ => false
    if let some group := Typing.StandardRow.groupOp name then
      return fun | .group op .. => op == group | _ => false
    if let some seq := Typing.StandardRow.seqOp name then
      return fun | .seq op .. => op == seq | _ => false
    if let some key := Typing.StandardRow.resolve ⟨name, #[]⟩ then return (· == key)
    match ← Typing.StandardRow.resolve ⟨name, #[.nat 0]⟩ with
    | .hash (.shake128 _) => return fun | .hash (.shake128 _) => true | _ => false
    | .hash (.shake256 _) => return fun | .hash (.shake256 _) => true | _ => false
    | _ => none
  guard (standard.isSome || check.state.results.rows.any (·.key.name == name))
  return .localOp fun _ => fun
    | .row (.inl key) => standard.any (· key)
    | .row (.inr key) => key.name == name
    | _ => false

/-- Loops are instructions and do not occur in the region's operation listing. -/
private partial def countLoops {Op Who : Type} (region : Zkc.Core.Region Op Who) : Nat :=
  let .mk _ steps _ := region
  steps.foldl (init := 0) fun total step => total + match step with
    | .choose _ _ _ _ yes no => countLoops yes + countLoops no
    | .cases _ _ _ _ arms => (arms.map countLoops).sum
    | .loop _ _ _ _ _ body => 1 + countLoops body
    | .block _ _ _ body | .attempt _ _ _ body => countLoops body
    | _ => 0

private def operationCount (p : SourcePackage) (operation : FixtureOperation) : Nat :=
  p.named.definitions.foldl (init := 0) fun total definition =>
    total + match definition, operation with
      | .fn _ _ _ _ _ _ body _, .loop => countLoops body
      | .protocol _ _ _ _ body, .loop => countLoops body
      | .fn _ _ _ _ _ _ body _, .localOp test => body.operations.countP (test p)
      | .protocol _ _ _ _ body, .localOp test => body.operations.countP fun
          | .compute _ op => test p op
          | _ => false

/-- Report core refusals, emission defects and exhausted checks. Individual cases specify
which roots should be admitted or waiting. -/
def checkPackages (label : String) (check : TypingCheck) : TestM Unit := do
  for report in check.packages do
    match report.outcome with
    | .refused source errors => failure s!"{label}: the core refuses the package of {report.description}: {source.describeRefusals errors}"
    | .defect message => failure s!"{label}: the package of {report.description} is not emitted: {message}"
    | .exhausted exhaustion =>
      failure s!"{label}: the package of {report.description} is not checked: {exhaustion.describe}"
    | _ => pure ()

/-- Count functions in the programs returned by admission. -/
def checkedFunctions (check : TypingCheck) : Nat :=
  check.packages.foldl (init := 0) fun count report =>
    match report.outcome with
    | .admitted p => count + p.admitted.program.headers.fns.length
    | _ => count

/-- The packages of protocol roots that the core admitted, with the check of facts of every
protocol and function in them, and the protocols those packages hold. -/
def checkedProtocols (check : TypingCheck) : Nat × Nat :=
  check.packages.foldl (init := (0, 0)) fun (roots, protocols) report =>
    match report.outcome, check.state.results.body? report.root with
    | .admitted package, some (.protocol _) => (roots + 1, protocols + package.admitted.program.headers.protocols.length)
    | _, _ => (roots, protocols)

/-- Checks the assertions `// uses`, `// not uses`, `// applies`, `// obligations`, `// waits` and
`// says`. -/
def checkTypingAssertions (label : String) (check : TypingCheck) (source : String) : TestM Unit := do
  let checkCount (name : String) (predicate : Nat → Bool) (message : Nat → String) : TestM Unit := do
    let some operation := resolveOperation check name | failure s!"{label}: unknown operation `{name}`"
    let count := (emittedPackages check).foldl (fun n p => n + operationCount p operation) 0
    expectTrue (predicate count) (message count)
  let waits := check.packages.filterMap fun report => match report.outcome with
    | .waiting reason => some reason
    | _ => none
  for line in source.splitOn "\n" do
    if line.startsWith "// uses " then
      let name := String.ofList (line.toList.drop 8)
      checkCount name (· > 0) fun _ => s!"{label}: no package applies `{name}`"
    else if line.startsWith "// not uses " then
      let name := String.ofList (line.toList.drop 12)
      checkCount name (· == 0) fun _ => s!"{label}: a package applies `{name}`"
    else if line.startsWith "// applies " then
      match (String.ofList (line.toList.drop 11)).splitOn " " with
      | [name, count] =>
        checkCount name (fun found => some found == count.toNat?) fun found =>
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
  let source := "module assertions\ndef f(x: nat) -> nat: x + 1\n"
  let .ok (check, _) := typeBlock ⟨"assertions", "accept", "", #[source]⟩
    | failure "operation assertions: the control did not type"
  for line in ["// not uses nat.ad", "// applies nat.ad 0"] do
    let (_, result) ← (checkTypingAssertions "control" check line).run {}
    expectTrue (result.passed == 0 && result.failures == #["control: unknown operation `nat.ad`"])
      s!"operation assertions: {line} must report an unknown name"
  let blocks := readBlocks typingCases
  for block in blocks do checkTypingBlock block
  note s!"{blocks.size} programs for the typing of bodies"

end Zkc.Tests.Frontend
