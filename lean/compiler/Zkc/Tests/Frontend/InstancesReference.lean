import Zkc.Tests.Frontend.NamesReference
import Zkc.Tests.Frontend.Instances

/-!
# The check of instances over the reference

The tests of layer A whose names resolve, every module of `lib/` as a root, the worked programs
with their example files, and the generated program of the measurements, instantiated from their
roots, their `// instantiate:` comments and the default instances of their public declarations.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- The rules that the check of instances decides. -/
def instanceRules : Array String :=
  #["NL1", "NL9", "SP3", "SP4", "SP5", "SP6", "SP8", "SP11", "GR5", "TY2"]

/-- The tests of layer A that the check of instances refuses: the rule and the line of the first
refusal, in the first module of the test. -/
def expectedInstanceRefusals : Array (String × String × Nat) := #[
  ("T-Z1b", "SP4", 3), ("S-Z2b", "SP4", 3), ("V-W1", "SP4", 4), ("N-SP4a", "SP4", 4),
  ("N-SP11b", "SP11", 2), ("N-SP11f", "SP11", 2), ("N-SP8a", "SP8", 5), ("N-SP8b", "SP8", 5),
  ("N-NL9b", "NL9", 5), ("N-NL9c", "NL9", 5), ("M-SUM14", "SP8", 42), ("M-FRA25", "SP11", 161),
  ("L-ALG1", "SP4", 52), ("L-ALG2", "SP3", 27), ("L-ALG4", "SP4", 52), ("L-HASH2", "SP8", 20),
  ("L-BLS1", "SP8", 14), ("T-Z2b", "TY2", 3), ("T-H8", "TY2", 3), ("S-Z2a", "TY2", 3),
  ("S-Z3", "TY2", 3), ("N-TY2c", "TY2", 3)]

/-- The tests of layer A whose refusal is by a rule of this check, and whose deciding needs a
body or the type of an expression: they pass this check. -/
def instancesWaitingForTyping : Array (String × String) := #[
  ("T-Z12", "the call `z()` in a body leaves `n` to inference from its arguments (SP6)"),
  ("T-F5", "the two functions reach each other through their bodies (NL1)"),
  ("S-X2", "the application of `Rounds` in a body leaves `n` to inference (SP6)"),
  ("R-SP3b", "the call `square(g)` in a body infers `F` from its argument (SP6, SP3)"),
  ("R-SP3c", "the member `G::identity` is named in a body"),
  ("N-SP11e", "the application in a body leaves out a specification-only parameter"),
  ("N-SP11i", "the application in a body gives a specification-only parameter as a deployed argument"),
  ("M-SUM4", "the application of `Reduce` in a body infers from a sum of two unknowns (SP6)"),
  ("M-GKR1", "the application of `Reduce` in a body infers from a product (SP6)"),
  ("R-TY2b", "the size `half` is a name bound in a body"),
  ("M-FRA6", "the size `half` is a `mut` name of a body")]

/-- The worked programs that the check of instances refuses: the rule, the file below
`programs/`, the line. `stark` reaches `support/fibonacci.zkc`, which binds a module to an asset
whose interface has type members: the form that the reference withdrew (NL9). -/
def expectedProgramRefusals : Array (String × String × String × Nat) := #[
  ("stark", "NL9", "support/fibonacci.zkc", 9)]

/-- The tests of layer A, from their names to their instances. -/
def conformanceInstancesSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let mut total := 0
  let mut beforeThis := 0
  let mut refusedHere : Array String := #[]
  let mut waiting : Array String := #[]
  let mut accepted := 0
  let mut seen : Array String := #[]
  let mut contradictions : Array (String × String) := #[]
  for path in ← sortedFiles (reference / "conformance") "txt" do
    unless (path.fileName.getD "").startsWith "layer-a-" do continue
    for block in readBlocks (← IO.FS.readFile path) do
      total := total + 1
      seen := seen.push block.id
      let .ok files := parseBlock block
        | beforeThis := beforeThis + 1
      let names := (List.range files.size).toArray.map fun index => s!"{block.id}.{index}"
      let inputs := (List.range files.size).toArray.map fun index =>
        ({ name := names[index]!, parsed := .ok files[index]! } : SourceInput)
      let nameCheck ← checkNames inputs fun names => (load names : IO _)
      unless nameCheck.refusals.isEmpty do
        beforeThis := beforeThis + 1
        continue
      let check := checkInstances nameCheck names
      let (own, library) := check.refusals.partition fun refusal => names.contains refusal.span.file
      for refusal in library do
        failure s!"{block.id} reaches a module of the library whose instances are refused: {refusal.span.file}: {refusal.render}"
      let rules := refusalRules block.expect
      if let some (_, rule, line) := expectedInstanceRefusals.find? (·.1 == block.id) then
        match own[0]? with
        | some first =>
          if first.rule == rule && first.span.file == names[0]! && first.span.startLine.toNat == line then
            pass
            refusedHere := refusedHere.push s!"{block.id} {rule} line {line}"
            if contradicts block.expect rule then
              contradictions := contradictions.push
                (block.id, s!"{block.id} expects `{block.expect}`; refused by {rule} at line {line}")
          else failure s!"{block.id}: expected a refusal by {rule} at line {line}; {first.span.file}: {first.render}"
        | none => failure s!"{block.id}: expected a refusal by {rule} at line {line}; the instances are formed"
      else
        let waits := instancesWaitingForTyping.find? (·.1 == block.id)
        if rules.any instanceRules.contains && waits.isNone then
          failure s!"{block.id}: expects `{block.expect}`, and neither a line nor a reason to wait for typing is recorded"
        else
          match own[0]? with
          | none =>
            pass
            if let some (_, reason) := waits then waiting := waiting.push s!"{block.id}: {reason}"
            else accepted := accepted + 1
          | some first =>
            failure s!"{block.id}: expects `{block.expect}`; refused by the check of instances: {first.span.file}: {first.render}"
  reportContradictions contradictions
  for (id, rule, _) in expectedInstanceRefusals do
    unless seen.contains id do failure s!"{id}: expected to be refused by {rule}; not found"
  note s!"{total} tests of layer A: {beforeThis} refused before this check, {refusedHere.size} refused by the check of instances as expected, {waiting.size} waiting for typing, {accepted} pass the check of instances"
  for entry in refusedHere do note s!"refused: {entry}"
  for entry in waiting do note s!"waiting for typing: {entry}"

/-- Every module of `lib/` as a root: its roots and the default instances of its public
declarations form, and their signatures evaluate. -/
def libraryInstancesSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let mut instances := 0
  let mut defaults := 0
  for path in ← sortedFiles (reference / "lib") "zkc" do
    let source ← IO.FS.readBinFile path
    let input : SourceInput := { name := path.toString, parsed := parse path.toString source }
    let nameCheck ← checkNames #[input] fun names => (load names : IO _)
    unless nameCheck.refusals.isEmpty do
      failure s!"{path}: the names do not resolve"
      continue
    let check := checkInstances nameCheck #[path.toString]
    if check.refusals.isEmpty then pass
    for refusal in check.refusals do
      failure s!"{path}: {refusal.span.file}: {refusal.render}"
    instances := instances + check.state.table.entries.size
    for entry in check.state.defaults do
      let declaration := nameCheck.program.declarations[entry.declaration]!
      if (nameCheck.program.files[declaration.file]?).any (·.name == path.toString) then
        defaults := defaults + entry.count
        if let some reason := entry.none? then
          note s!"{path.fileName.getD ""}: no default instance of `{nameCheck.program.nameOf entry.declaration}`: {reason}"
  note s!"modules of lib/: {instances} instances, {defaults} default instances of their own declarations"

/-- What some instances of the worked programs hold. -/
def programContents : Array (String × String × String) := #[
  ("schnorr", "Schnorr<G = G1>", "(base: G1, point: G1, scalar: Fr) -> ()"),
  ("schnorr", "DLog<G = G1>", "(base: G1, point: G1, scalar: Fr) -> bool"),
  ("sumcheck", "Reduce<F = Fr, R = Pairs<Fr>, v = 0, k = 0, rounds = 10>",
    "(p: MvPoly<Fr, 10, 1>, state: [Fr; 1024], prefix: [Fr; 0], claim: Fr) -> (point: [Fr; 10], value: Fr, residual: [Fr; 1])"),
  ("sumcheck", "Pairs<F = Fr>",
    "Round<Fr>: Degree = 1, State defined, Message = (Fr, Fr), message defined, bind defined, boundary defined, evaluate defined, table defined, polynomial defined"),
  ("sumcheck", "sums<F = Fr, v = 2>", "(table: [Fr; 8]) -> (Fr, Fr)")]

/-- Every worked program with its example file. -/
def programInstancesSuite (reference : System.FilePath) : TestM Unit := do
  let programs := reference / "programs"
  let load ← cachedLoader #[reference / "lib", programs, programs / "support"]
  for path in ← sortedFiles programs "zkc" do
    let stem := path.fileStem.getD ""
    if stem.endsWith "_example" || path.parent != some programs then continue
    let exampleFile := programs / s!"{stem}_example.zkc"
    let files := if ← exampleFile.pathExists then #[path, exampleFile] else #[path]
    let inputs ← files.mapM fun file => do
      let source ← IO.FS.readBinFile file
      return ({ name := file.toString, parsed := parse file.toString source } : SourceInput)
    let nameCheck ← checkNames inputs fun names => (load names : IO _)
    unless nameCheck.refusals.isEmpty do
      failure s!"{stem}: the names do not resolve"
      continue
    let check := checkInstances nameCheck (files.map (·.toString))
    match expectedProgramRefusals.find? (·.1 == stem) with
    | some (_, rule, file, line) =>
      let expectedFile := (programs / file).toString
      match check.refusals with
      | #[refusal] =>
        if refusal.rule == rule && refusal.span.file == expectedFile && refusal.span.startLine.toNat == line then
          pass
          note s!"{stem}: refused by {rule} at {file}:{line}, as expected"
        else failure s!"{stem}: expected a refusal by {rule} at {file}:{line}; {refusal.span.file}: {refusal.render}"
      | refusals =>
        failure s!"{stem}: expected one refusal by {rule} at {file}:{line}; found {refusals.size}"
        for refusal in refusals do failure s!"{stem}: {refusal.span.file}: {refusal.render}"
    | none =>
      if check.refusals.isEmpty then
        pass
        let described := describedInstances check
        let unevaluated := (described.filter fun (_, content) => content.contains '?').size
        note s!"{stem}: {check.state.table.entries.size} instances, {unevaluated} with a type not evaluated here"
        for (program, description, expected) in programContents do
          if program != stem then continue
          match described.find? (·.1 == description) with
          | some (_, found) =>
            expectTrue (found == expected) s!"{stem}: `{description}` holds `{found}`, expected `{expected}`"
          | none => failure s!"{stem}: no instance `{description}`"
      for refusal in check.refusals do failure s!"{stem}: {refusal.span.file}: {refusal.render}"

/-- The generated program of the measurements: its instances form. -/
def generatedInstancesSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let text := Zkc.Tools.Frontend.Generate.program 50000
  let input : SourceInput := { name := "generated", parsed := parseString "generated" text }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  let check := checkInstances nameCheck #["generated"]
  if nameCheck.refusals.isEmpty && check.refusals.isEmpty then pass
  for refusal in (nameCheck.refusals ++ check.refusals).extract 0 5 do
    failure s!"the generated program: {refusal.span.file}: {refusal.render}"
  note s!"generated program: {check.state.table.entries.size} instances"

/-- An instance whose `where` cannot be evaluated here waits, and says for what (SP4): a
constraint over a member that a module bound to the vocabulary does not give. -/
def waitingInstanceSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let text := "module waiting\n\nuse zkc::suites::{Merlin3Bls12381}\nuse zkc::construction::{Suite}\n\npub def f<S: Suite>() -> nat where (S::Units != S::Units): 1\n\npub def top() -> nat: f<Merlin3Bls12381>()\n"
  let input : SourceInput := { name := "waiting", parsed := parseString "waiting" text }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  let check := checkInstances nameCheck #["waiting"]
  expectTrue (nameCheck.refusals.isEmpty && check.refusals.isEmpty) "a `where` that waits refuses nothing"
  let expected := "waits for a constraint of its `where`: the member `Units` of a module bound to the vocabulary or to an asset"
  match (describedInstances check).find? (·.1 == "f<S = Merlin3Bls12381>") with
  | some (_, found) =>
    expectTrue (found == expected) s!"the instance whose `where` waits holds `{found}`, expected `{expected}`"
  | none => failure "no instance `f<S = Merlin3Bls12381>`"

end Zkc.Tests.Frontend
