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

/-- A source spelling of an instance key for fixture expectations. Table indices are local to
one compilation. Resolve each one through that compilation, including nested arguments and
the implementing owner of a law. A vocabulary type is identified by its row. -/
private def withArguments (name : String) (args : List String) : String :=
  if args.isEmpty then name else s!"{name}<{", ".intercalate args}>"

private def parameterName (state : Compile.State) (param : ParameterRef) : String := Id.run do
  let scope := state.program.scopes[param.scope]!
  let parameter := scope.parameters[param.index]!
  let owner := match state.scopeOwners[param.scope]? with
    | some decl => Static.qualifiedName state.program decl
    | none =>
      -- An anonymous section has no declaration. Locate its binder in the named file module.
      let path := "::".intercalate state.program.files[scope.file]!.path.toList
      s!"{path}#section@{parameter.span.startByte}"
  return s!"{owner}::{parameter.name.text}"

mutual
  private partial def instanceName (state : Compile.State) (root : InstanceId) : String := Id.run do
    let key := state.table.allocatedKey! root
    let name := Static.qualifiedName state.program key.declaration
    let args := key.arguments.toList.map (valueName state) ++ key.specification.toList.map (s!"spec {·}")
    let mut result := withArguments name args
    if let some view := key.view then result := s!"{result}#{view.member}"
    if let some (param, members) := key.opaqueFor then
      result := s!"{result}#opaque({parameterName state param}, {reprStr members.toList})"
    if let some owner := key.owner then result := s!"{result} at {instanceName state owner}"
    return result

  private partial def valueName (state : Compile.State) : StaticValue → String
    | .natural n => toString n
    | .module id => instanceName state id
    | .type ty => typeName state ty

  private partial def typeName (state : Compile.State) : ClosedType → String
    | .bool => "bool"
    | .nat => "nat"
    | .rational => "rational"
    | .index n => s!"index<{n}>"
    | .nonzero ty => s!"nonzero<{typeName state ty}>"
    | .seq ty none => s!"[{typeName state ty}]"
    | .seq ty (some n) => s!"[{typeName state ty}; {n}]"
    | .tuple types names =>
      let fields := types.zipWith (fun ty name => (name.map (· ++ ": ")).getD "" ++ typeName state ty) names
      s!"({", ".intercalate fields.toList})"
    | .nominal row args => withArguments s!"row({reprStr row})" (args.toList.map (valueName state))
    | .record id | .variant id | .specification id => instanceName state id
    | .opaque owner member args _ =>
      withArguments s!"({instanceName state owner})::{member}" (args.toList.map (valueName state))
end

/-- Count reports even when the block has a source refusal in another declaration. -/
def recordTypingRoots (label : String) (check : TypingCheck) : TestM Unit := do
  for report in check.packages do
    let outcome : UnpackagedOutcome ← match report.outcome with
      | .admitted _ =>
        modify fun t => {t with admittedRoots := t.admittedRoots + 1}
        continue
      | .waiting reason => pure (.waiting reason)
      | .typedOnly reason => pure (.typedOnly reason)
      | _ => continue -- checkPackages reports refusals, emission defects and exhaustion.
    let declaration := Static.qualifiedName check.state.program (check.state.table.allocatedKey! report.root).declaration
    let root : UnpackagedRoot := {
      block := label, declaration, instanceName := instanceName check.state report.root, outcome
      description := Typing.rootDescription check.state report.root true }
    modify fun t => {t with unpackagedRoots := t.unpackagedRoots.push root}

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

/-- Check the source annotations about packages, operations, obligations and diagnostics. -/
def checkTypingAssertions (label : String) (check : TypingCheck) (source : String) : TestM Unit := do
  let checkCount (name : String) (predicate : Nat → Bool) (message : Nat → String) : TestM Unit := do
    let some operation := resolveOperation check name | failure s!"{label}: unknown operation `{name}`"
    let count := (emittedPackages check).foldl (fun n p => n + operationCount p operation) 0
    expectTrue (predicate count) (message count)
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
    else if line.startsWith "// sole package " then
      let name := (line.drop "// sole package ".length).toString
      let admitted := check.packages.filterMap fun report =>
        if report.outcome matches .admitted _ then
          some (instanceName check.state report.root, Typing.rootDescription check.state report.root true)
        else none
      expectTrue (admitted.map Prod.fst == #[name])
        s!"{label}: expected only the package of {name}, found {admitted.map fun (id, description) => describeExpectedInstance id description}"
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
      let reason := (line.drop 9).toString
      let waits := check.packages.filterMap fun report => match report.outcome with
        | .waiting text => some text
        | _ => none
      expectTrue (waits.any (·.contains reason))
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
    | none => pass
  | ["wait"] =>
    match check.refusals[0]? with
    | some first => failure s!"{block.id}: expected to wait; {first.span.file}: {first.render}"
    | none =>
      expectTrue (check.packages.any (fun report => report.outcome matches .waiting _))
        s!"{block.id}: expected a waiting root"
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
  recordTypingRoots block.id check
  checkPackages block.id check
  for text in block.files do checkTypingAssertions block.id check text

private def expectedFixtureRoots : List ExpectedRoot :=
  let quotient := UnpackagedOutcome.waiting "the quotient of `rational`s"
  [⟨"rational", .one "t::bound", .waiting "the sum of `rational`s"⟩,
   ⟨"rational", .one "t::small", .waiting "specification type in executable code"⟩,
   ⟨"mixed-roots", .one "t::half", quotient⟩,
   ⟨"guarded-rational-index", .one "t::half", quotient⟩,
   ⟨"unguarded-rational-index", .one "t::half", quotient⟩,
   ⟨"static-rational-index", .one "t::half", quotient⟩,
   ⟨"formal-signature-facts", .one "t::r", .waiting "specification type in executable code"⟩]

/-- These checks intentionally give the driver a stale or incomplete expectation. Check
the diagnostics themselves, including the instance that moved in source order. -/
private def rootAccountingControls : TestM Unit := do
  let half := "spec def half(x: nat) -> rational: x / 2\n"
  let other := "spec def other(x: nat) -> rational: x / 3\n"
  let reason := "the quotient of `rational`s"
  let expected : List ExpectedRoot := [⟨"accounting", .one "t::half", .waiting reason⟩]
  for (body, message) in [(half ++ other, s!"accounting: unexpected t::other: waiting for {reason}"),
      (other ++ half, s!"accounting: unexpected t::other: waiting for {reason}"),
      ("spec def half(b: bool) -> bool: b\n", s!"accounting: t::half: waiting for {reason}; missing 1 expected")] do
    let block : Block := ⟨"accounting", "accept", "", #["module t\n" ++ body]⟩
    let (_, result) ← (do checkTypingBlock block; checkExpectedRoots expected #["accounting"]).run {}
    expectTrue (result.failures == #[message])
      s!"root accounting: expected {message}, got {result.failures}"

/-- An exact instance and its remaining family match in either order. -/
private def namedInstanceAndFamily : TestM Unit := do
  let outcome := UnpackagedOutcome.waiting "specification type in executable code"
  let named : UnpackagedRoot := {block := "mixed instances", declaration := "t::f", instanceName := "t::f<1>", outcome := outcome}
  let sibling : UnpackagedRoot := {block := "mixed instances", declaration := "t::f", instanceName := "t::f<2>", outcome := outcome}
  let one : ExpectedRoot := ⟨"mixed instances", .one named.instanceName, outcome⟩
  let family : ExpectedRoot := ⟨"mixed instances", .family named.declaration 1, outcome⟩
  for reports in [#[named, sibling], #[sibling, named]] do
    for expectations in [[one, family], [family, one]] do
      let (_, result) ← (checkExpectedRoots expectations #["mixed instances"]).run {unpackagedRoots := reports}
      expectTrue (result.passed == 2 && result.failures.isEmpty)
        s!"mixed instances: report order {reports.map (·.instanceName)}; {result.failures}"

/-- The same local name in another module denotes a different owner or argument. Exercise
the checker with both modules and the same exact expectation. -/
private def qualifiedInstanceControls : TestM Unit := do
  let iface := "module common\npub interface I:\n    def identity(x: bool) -> bool\n    law bounded(x: rational): x <= 1 / 2\n"
  let leftLaw := "common::I::bounded at left::M"
  let waits := UnpackagedOutcome.waiting "a comparison of `rational`s"
  for ns in ["left", "right"] do
    let impl := "module " ++ ns ++ "\nuse common::{I}\npub module M: I:\n    def identity(x): x\n"
    let (_, law) ← (do
      checkTypingBlock ⟨"law", "accept", "", #[iface, impl]⟩
      checkExpectedRoots [⟨"law", .one leftLaw, waits⟩] #["law"]).run {}
    if ns == "left" then expectTrue law.failures.isEmpty s!"law at left::M: {law.failures}"
    else
      expectTrue (law.failures.size == 2 && law.failures[0]!.contains "common::I::bounded at right::M" &&
        law.failures[1]!.contains leftLaw) s!"law at right::M: {law.failures}"
    let client := "module client\nuse " ++ ns ++ "::{Box}\ndef run<T>(x: T) -> T: x\n" ++
      "// instantiate: run<Box>\n// sole package client::run<left::Box>\n"
    let record := s!"module {ns}\npub struct Box:\n    x: nat\n"
    let (_, sole) ← (checkTypingBlock ⟨"argument", "accept", "", #[client, record]⟩).run {}
    if ns == "left" then expectTrue sole.failures.isEmpty s!"package at left::Box: {sole.failures}"
    else
      expectTrue (sole.failures.size == 1 && sole.failures[0]!.contains "client::run<right::Box>")
        s!"package at right::Box: {sole.failures}"

def typingCaseSuite : TestM Unit := do
  rootAccountingControls
  qualifiedInstanceControls
  namedInstanceAndFamily
  let source := "module assertions\ndef f(x: nat) -> nat: x + 1\n"
  let .ok (check, _) := typeBlock ⟨"assertions", "accept", "", #[source]⟩
    | failure "operation assertions: the control did not type"
  for line in ["// not uses nat.ad", "// applies nat.ad 0"] do
    let (_, result) ← (checkTypingAssertions "control" check line).run {}
    expectTrue (result.passed == 0 && result.failures == #["control: unknown operation `nat.ad`"])
      s!"operation assertions: {line} must report an unknown name"
  let blocks := readBlocks typingCases
  for block in blocks do checkTypingBlock block
  checkExpectedRoots expectedFixtureRoots (blocks.map (·.id))
  note s!"{blocks.size} programs for the typing of bodies"

end Zkc.Tests.Frontend
