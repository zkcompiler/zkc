import Zkc.Tests.Frontend.InstancesReference
import Zkc.Tests.Frontend.Typing

/-!
# The typing of bodies over the reference

The tests of layer A whose names resolve and whose instances form, typed and elaborated to the
core; every module of `libraries/` as a root at its default instances; the worked programs with their
example files; the generated program of the measurements. Every package emitted is elaborated by
the core, and every function of it passes the core's check of facts.

Each block retains its expected program verdict. Source refusals name their rule and line.
Package reports of its reached roots are counted separately as admitted, waiting or typed only. A test whose roots wait for a form that is
not elaborated yet waits, with the reasons of its roots. A refusal by a rule that is neither the
one a test expects nor its stated alternative is a contradiction: listed, and a failure unless the
table of known contradictions gives its reason. A test of acceptance that no root reaches is
neither accepted nor refused here, and is listed apart.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- The tests of layer A that the typing of bodies refuses: the rule and the line of the first
refusal, in the first module of the test. -/
def expectedTypingRefusals : Array (String × String × Nat) := #[
  ("T-P6", "SX3", 3), ("T-F1", "FN1", 3), ("R-FN5b", "FN5", 3), ("V-K1", "FN5", 3),
  ("V-K2", "FN5", 4), ("N-FN5a", "FN5", 3), ("S-Z1", "CT6", 5), ("T-Z12", "SP6", 5),
  ("T-F4", "SP9", 5), ("T-F5", "NL1", 3), ("S-K3", "NL6", 2), ("R-SP7e", "NL6", 2),
  ("R-SP3b", "SP3", 3), ("R-SP3c", "SP3", 3), ("R-NL6a", "NL6", 3), ("R-NL6b", "NL6", 3),
  ("R-NL6d", "NL6", 7), ("M-FRA2", "NL6", 37), ("L-SEQ4", "NL6", 36), ("T-Z6", "TY7", 3),
  ("T-Z10", "TY10", 5), ("I-4b", "TY7", 3), ("I-4c", "TY7", 5), ("I-4f", "TY7", 8),
  ("I-8c", "TY13", 7), ("R-TY8c", "TY1", 2), ("R-TY2b", "TY2", 5), ("R-SP7b", "TY7", 2),
  ("R-TY6a", "TY6", 3), ("R-TY6b", "TY6", 3), ("R-TY9b", "TY7", 3), ("R-TY16b", "TY7", 3),
  ("V-F1", "TY7", 7), ("V-F1b", "TY7", 7), ("V-F1c", "TY7", 7), ("V-F5", "TY8", 2),
  ("V-F5b", "TY8", 2), ("V-F5c", "TY7", 3), ("V-F7", "TY7", 8),
  ("V-F9", "TY7", 6), ("V-F10", "TY7", 8), ("V-F11", "TY7", 5), ("V-F15", "TY8", 3),
  ("N-TY9a", "TY7", 3), ("N-TY9d", "TY7", 3), ("N-TY9e", "TY7", 6), ("N-TY6d", "TY6", 3),
  ("N-SP7a", "TY7", 2), ("N-TY10c", "TY8", 5), ("N-TY13a", "TY13", 12), ("N-TY8f", "TY8", 2),
  ("N-TY8h", "TY8", 3), ("M-SUM1", "TY7", 15), ("M-FRA1", "TY13", 21),
  ("M-FRA4", "TY7", 47), ("M-FRA5", "TY7", 52), ("M-FRA6", "TY5", 64), ("M-FRA7", "TY6", 68),
  ("M-FRA15", "TY7", 126), ("M-FRA16", "TY5", 130), ("M-FRA17", "TY7", 139),
  ("M-FRA18", "TY8", 144), ("M-FRA19", "TY7", 152), 
  ("L-SEQ3", "TY7", 11), ("L-SEQ5", "TY5", 46), ("L-MLE1", "TY5", 12), ("L-COS1", "TY8", 21),
  ("L-COS2", "TY5", 44), ("L-COS3", "TY5", 52), ("R-TY8b", "TY8", 2), ("V-E3", "SX2", 3),
  ("T-F2", "FN3", 5), ("M-FRA8", "TY8", 79), ("N-SP10f", "SP10", 3), ("M-SUM8", "SP9", 41),
  ("M-SUM12", "NL6", 30), ("N-NL6b", "NL6", 10), ("N-SP12a", "SP12", 8), ("N-SP12c", "SP12", 8),
  ("N-SP12g", "SP12", 8), ("N-TY6g", "TY6", 8), ("X-SP12a", "SP12", 15), ("M-FRA21", "SP12", 176),
  ("M-FRA22", "NL6", 176), ("N-SP10b", "TY7", 4),
  -- protocol bodies
  ("T-X1", "SX2", 4), ("T-X2", "SX4", 5), ("M-SUM3", "SX4", 82), ("T-P7", "EV1", 4),
  ("T-H1", "HO1", 3), ("T-H3", "HO2", 3), ("T-H4", "EV5", 3), ("T-H5", "GU2", 3),
  ("T-H7", "CT2", 3), ("T-E1", "EV3", 5), ("T-E1b", "EV3", 4),
  ("T-E7", "RM1", 5), ("T-E9", "HO5", 3), ("S-A1", "GU2", 8), ("S-A1b", "GU2", 8),
  ("I-5c", "CT2", 6), ("R-EV1b", "EV1", 7), ("R-EV1c", "EV1", 5),
  ("M-SCH2", "TY5", 23), ("T-H10", "TY4", 5), ("I-3", "TY15", 3),
  ("I-4d", "TY4", 5), ("V-F2", "TY4", 5), ("V-F3", "TY7", 6), ("V-H1", "TY7", 6),
  ("V-H2", "TY5", 6), ("V-H3", "TY7", 6), ("N-TY14c", "TY7", 7),
  ("M-FRA23", "TY7", 183), ("M-FRA24", "TY7", 192), ("T-H9", "EV5", 5), ("I-8a", "CT2", 7),
  ("M-SUM2", "GU2", 61), ("M-SUM7", "HO1", 63), ("M-SUM13", "GU2", 61), ("M-FRA10", "RM1", 100),
  ("M-FRA12", "HO1", 105), ("M-OR1", "CT2", 18), ("M-OR2", "TY13", 34), ("N-SP11e", "SP11", 5),
  ("N-SP11i", "SP11", 5), ("M-IPA1", "TY5", 48), ("M-IPA6", "NL6", 18), ("M-IPA7", "NL6", 51),
  ("L-POLY1", "TY7", 19), ("S-X2", "SP6", 11), ("M-SUM4", "SP6", 82), ("N-TY16a", "TY7", 5),
  ("M-SUM6", "TY5", 65), ("M-SUM11", "TY5", 65), ("M-IPA2", "TY7", 56), ("M-IPA9", "TY5", 88),
  ("M-GKR1", "SP6", 36), ("M-GKR3", "TY8", 27)]

/-- External functions have a typed header at each default instance. Check the full reason,
including the named arguments, against the field and natural parameters of the fixture. -/
private def externalRoots (block qualified : String) (naturals : List String) : List ExpectedRoot :=
  let assignments := naturals.foldr (init := [[]]) fun _ rest =>
    ["0", "1", "2", "3"].flatMap fun n => rest.map (n :: ·)
  assignments.map fun values =>
    let args := ", ".intercalate ("row(\"koala-bear\")" :: values)
    let named := naturals.zipWith (fun k v => s!"{k} = {v}") values
    let name := (qualified.splitOn "::").getLast!
    let reason := s!"external function {name}<{", ".intercalate ("F = koala-bear" :: named)}>"
    ⟨block, .one s!"{qualified}<{args}>", .typedOnly reason⟩

/-- PartialSum has four defaults for each of its three natural parameters. The laws are
instantiated at Pairs, and also at Gate in GKR. A refused law has no waiting report. -/
private def sumcheckRoots (block : String) (owners : List String) (refusedLaw : Option String) :
    List ExpectedRoot := Id.run do
  let outcome := UnpackagedOutcome.waiting "specification type in executable code"
  let mut roots := [⟨block, .family "sumcheck::PartialSum" 64, outcome⟩]
  for owner in owners do
    for law in ["sent", "bound", "ends", "at_point"] do
      if refusedLaw == some law then continue
      let field := "row(\"koala-bear\")"
      let arguments := if law == "sent" || law == "bound" then
        [0, 1, 2, 3].map fun (n : Nat) => s!"{field}, {n}" else [field]
      for args in arguments do
        let name := s!"sumcheck::Round::{law}<{args}> at {owner}<{field}>"
        roots := ⟨block, .one name, outcome⟩ :: roots
  return roots

/-- Expected non-package reports, independent of the frozen program verdict. Sibling
declarations are compared even in a block which refuses its named source rule. -/
def knownWaits : List ExpectedRoot :=
  let specification := UnpackagedOutcome.waiting "specification type in executable code"
  [⟨"V-K2", .one "t::at_one", specification⟩, ⟨"T-Z13", .one "t::r", specification⟩,
   ⟨"R-NL9b", .one "t::check", specification⟩,
   ⟨"R-TY8a", .one "t::bound", .waiting "the sum of `rational`s"⟩,
   ⟨"R-SP3a", .one "t::loss", .waiting "the quotient of `rational`s"⟩] ++
  (["M-FRA1", "M-FRA2", "M-FRA3", "M-FRA4", "M-FRA5", "M-FRA6", "M-FRA7", "M-FRA10",
    "M-FRA12", "M-FRA14", "M-FRA15", "M-FRA16", "M-FRA17", "M-FRA18", "M-FRA19",
    "M-FRA21", "M-FRA22", "M-FRA23", "M-FRA24"].map fun block =>
    ⟨block, .one "fragments::birthday", .waiting "the quotient of `rational`s"⟩) ++
  (["M-SUM2", "M-SUM3", "M-SUM4", "M-SUM6", "M-SUM7", "M-SUM11", "M-SUM13"].flatMap fun block =>
    sumcheckRoots block ["sumcheck::Pairs"] none) ++
  sumcheckRoots "M-SUM1" ["sumcheck::Pairs"] (some "sent") ++ sumcheckRoots "M-SUM8" ["sumcheck::Pairs"] (some "at_point") ++
  sumcheckRoots "M-SUM12" ["sumcheck::Pairs"] (some "ends") ++
  (["M-GKR1", "M-GKR2", "M-GKR3"].flatMap fun block =>
    sumcheckRoots block ["sumcheck::Pairs", "circuits::layered::Gate"] none ++ externalRoots block "circuits::layered::summand" ["d", "w"]) ++
  ([("cube", ["n"]), ("evaluate_at", ["n", "D"]), ("extension", ["v"]), ("first_variable", ["n", "D"]),
    ("line", []), ("of_coefficients", ["D"]), ("restrict", ["n", "D"]), ("restrict_prefix", ["n", "k", "D"]),
    ("value", ["D"])].flatMap fun (name, parameters) => externalRoots "L-POLY1" s!"zkc::polynomial::{name}" parameters)

/-- A reference refusal deferred by a waiting body, identified by its block and rule. -/
private def deferredRefusals : List (String × String) := []

private def checkWaitingVerdict (block : Block) (deferred : List (String × String)) :
    TestM (Option (String × String)) := do
  if block.expect.startsWith "accept" then
    pass
    return none
  if let some entry := deferred.find? fun (id, rule) => id == block.id && block.expect == s!"refuse {rule}" then
    pass
    note s!"{block.id}: a waiting root defers the reference refusal {entry.2}"
    return some entry
  failure s!"{block.id}: expects `{block.expect}`; roots wait and no source refusal was reported"
  return none

private def waitingVerdictControls : TestM Unit := do
  let block : Block := ⟨"bound", "refuse TY7", "", #[]⟩
  for (exceptions, allowed) in [([], false), ([("bound", "TY7")], true),
      ([("bound", "TY5")], false), ([("other", "TY7")], false)] do
    let (matched, result) ← (checkWaitingVerdict block exceptions).run {}
    let ok := if allowed then matched == some ("bound", "TY7") && result.failures.isEmpty
      else matched.isNone && result.failures.size == 1 && result.failures[0]!.contains "refuse TY7"
    expectTrue ok s!"waiting block with reference refusal: {result.failures}"

/-- The tests of layer A, from their instances to the core. -/
def conformanceTypingSuite (repository : Repository) : TestM Unit := do
  waitingVerdictControls
  let load ← cachedLoader #[repository.libraries]
  let mut total := 0
  let mut beforeThis := 0
  let mut refusedHere : Array String := #[]
  let mut waiting := 0
  let mut deferred := #[]
  let mut accepted := 0
  let mut checkedTotal := 0
  let mut seen : Array String := #[]
  let mut contradictions : Array (String × String) := #[]
  let mut unreached : Array String := #[]
  let mut protocolRootsTotal := 0
  let mut protocolsTotal := 0
  for path in ← sortedFiles (repository.conformance) "txt" do
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
      let instances := checkInstances nameCheck names
      unless instances.refusals.isEmpty do
        beforeThis := beforeThis + 1
        continue
      let check := checkTyping instances names
      recordTypingRoots block.id check
      checkPackages block.id check
      let checked := checkedFunctions check
      checkedTotal := checkedTotal + checked
      let (roots, protocols) := checkedProtocols check
      protocolRootsTotal := protocolRootsTotal + roots
      protocolsTotal := protocolsTotal + protocols
      let (own, library) := check.refusals.partition fun refusal => names.contains refusal.span.file
      for refusal in library do
        failure s!"{block.id} reaches a module of the library whose typing is refused: {refusal.span.file}: {refusal.render}"
      let accepts := block.expect.startsWith "accept"
      match expectedTypingRefusals.find? (·.1 == block.id), own[0]? with
      | some (_, rule, line), some first =>
        if first.rule == rule && first.span.file == names[0]! && first.span.startLine.toNat == line then
          pass
          refusedHere := refusedHere.push s!"{block.id} {rule} line {line}"
          if contradicts block.expect rule then
            contradictions := contradictions.push
              (block.id, s!"{block.id} expects `{block.expect}`; refused by {rule} at line {line}")
        else failure s!"{block.id}: expected a refusal by {rule} at line {line}; {first.span.file}: {first.render}"
      | some (_, rule, line), none =>
        failure s!"{block.id}: expected a refusal by {rule} at line {line}; the bodies type"
      | none, some first =>
        failure s!"{block.id}: expects `{block.expect}`; refused by the typing of bodies: {first.span.file}: {first.render}"
      | none, none =>
        if check.packages.any (fun report => report.outcome matches .waiting _) then
          if let some entry ← checkWaitingVerdict block deferredRefusals then deferred := deferred.push entry
          waiting := waiting + 1
        else if check.packages.isEmpty && check.state.results.finished.isEmpty then
          -- nothing reaches a body: neither an acceptance nor a refusal by this check
          if accepts then
            pass
            unreached := unreached.push block.id
          else failure s!"{block.id}: expects `{block.expect}`; no root reaches a body"
        else if !accepts then
          failure s!"{block.id}: expects `{block.expect}`; there is no typing refusal or waiting root"
        else
          pass
          accepted := accepted + 1
  for entry in deferredRefusals do
    unless deferred.contains entry do failure s!"{entry.1}: missing deferred refusal {entry.2}"
  checkExpectedRoots knownWaits seen
  reportContradictions contradictions
  for (id, rule, _) in expectedTypingRefusals do
    unless seen.contains id do failure s!"{id}: expected to be refused by {rule}; not found"
  note s!"{total} tests of layer A: {beforeThis} refused before this check, {refusedHere.size} refused by the typing of bodies as expected, {waiting} with waiting roots, {accepted} accept cases with reached bodies and no waits, {unreached.size} accept cases with no reached body"
  note s!"no root reaches a body: {" ".intercalate unreached.toList}"
  note s!"functions in packages admitted by the core: {checkedTotal}"
  note s!"packages of protocol roots admitted with the check of facts of their protocols: {protocolRootsTotal}, holding {protocolsTotal} protocols"
  for entry in refusedHere do note s!"refused: {entry}"

/-- The refusals of modules of `libraries/` that the reference names as its own: the root's file stem,
the file refused, the rule and the line. `canonical::read_natural` of `zkc::layout` forms its
value in a `mut` accumulator, a `nat` about which no fact is made; the module's own note says
it is to change (layer C, not frozen). The law `natural` of `Layout`, typed at `canonical`,
reaches it. -/
def expectedLibraryRefusals : Array (String × String × String × Nat) := #[
  ("layout", "layout.zkc", "TY8", 46), ("suites", "layout.zkc", "TY8", 46)]

/-- Check the admitted operation of a caller using the catalogue's pairing module. -/
def pairingMemberSuite (repository : Repository) : TestM Unit := do
  let text := "module caller\nuse zkc::curves::bls12_381::{Bls12381, G1, G2, Gt}\n" ++
    "def evaluate(a: G1, b: G2) -> Gt: Bls12381::pair(a, b)\n"
  let load ← cachedLoader #[repository.libraries]
  let session ← Driver.Session.start.compile #[⟨"caller", parseString "caller" text⟩] fun names => (load names : IO _)
  let .ok roots := (session.admitRoots (some #["evaluate"])).complete
    | failure s!"pairing caller was not admitted: {session.renderDiagnostics}"
  let some p := roots.find? "evaluate" | failure "missing pairing caller"
  let some (.fn _ _ _ _ _ _ body _) := p.named.definitions.getLast? | failure "missing caller body"
  expectTrue ((body.operations matches [.row (.inl .pair)]) && p.bindings.rows.isEmpty)
    "the caller must apply the standard pairing row with no project binding"

/-- The modules of `libraries/` whose every function must be admitted at its default instances. -/
def admittedModules : Array String := #["prelude", "option", "algebra", "sequence"]

/-- Every module of `libraries/` as a root: its bodies type, and the packages of its default instances
are admitted or wait; those of `prelude`, `option`, `algebra` and `sequence` are all admitted. -/
def libraryTypingSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  for path in ← sortedFiles (repository.libraries) "zkc" do
    let stem := path.fileStem.getD ""
    let source ← IO.FS.readBinFile path
    let input : SourceInput := { name := path.toString, parsed := parse path.toString source }
    let nameCheck ← checkNames #[input] fun names => (load names : IO _)
    unless nameCheck.refusals.isEmpty do
      failure s!"{path}: the names do not resolve"
      continue
    let check := checkTyping (checkInstances nameCheck #[path.toString]) #[path.toString]
    if check.refusals.isEmpty then pass
    for refusal in check.refusals do
      let recorded := expectedLibraryRefusals.any fun (root, file, rule, line) =>
        root == stem && refusal.span.file.endsWith s!"/{file}" && refusal.rule == rule &&
          refusal.span.startLine.toNat == line
      if recorded then
        pass
        note s!"{stem}: refused as recorded: {refusal.span.file}: {refusal.render}"
      else failure s!"{path}: {refusal.span.file}: {refusal.render}"
    checkPackages stem check
    let checked := checkedFunctions check
    let mut admitted := 0
    let mut waits : Array String := #[]
    for report in check.packages do
      match report.outcome with
      | .admitted _ => admitted := admitted + 1
      | .waiting reason => unless waits.contains reason do waits := waits.push reason
      | _ => pure ()
    let required := admittedModules.contains stem && (path.parent.bind (·.fileName)) == some "zkc"
    if required then
      expectTrue waits.isEmpty s!"{stem}: a default instance waits: {waits}"
      -- every public function has an admitted default instance
      let program := nameCheck.program
      for index in [0:program.declarations.size] do
        let declaration := program.declarations[index]!
        unless declaration.kind == .function && declaration.pub do continue
        unless (program.files[declaration.file]?).any (·.name == path.toString) do continue
        let isRow := match declaration.node with
          | .«def» node => (node.binding matches .primitive _)
          | _ => false
        if isRow then continue
        let name := program.nameOf index
        let found := check.packages.any fun report =>
          (report.outcome matches .admitted _) &&
            (check.state.table.entries[report.root]?).any (·.key.declaration == index)
        expectTrue found s!"{stem}: `{name}` has no admitted package"
    let typedOnly := (check.packages.filter fun report => report.outcome matches .typedOnly _).size
    note s!"{stem}: {check.packages.size} packages, {admitted} admitted, {typedOnly} typed only{if waits.isEmpty then "" else s!", waiting for {", ".intercalate waits.toList}"}; {checked} functions in admitted packages; {check.state.results.obligations.size} obligations of laws"

/-- Every worked program with its example file: its bodies type, except where the check of
instances refuses it, and its packages are admitted or wait. -/
def programTypingSuite (repository : Repository) : TestM Unit := do
  let programs := repository.examples
  let load ← cachedLoader #[repository.libraries, programs, programs / "support"]
  for path in ← sortedFiles programs "zkc" do
    let stem := path.fileStem.getD ""
    if stem.endsWith "_example" || path.parent != some programs then continue
    if expectedProgramRefusals.any (·.1 == stem) then continue
    let exampleFile := programs / s!"{stem}_example.zkc"
    let files := if ← exampleFile.pathExists then #[path, exampleFile] else #[path]
    let inputs ← files.mapM fun file => do
      let source ← IO.FS.readBinFile file
      return ({ name := file.toString, parsed := parse file.toString source } : SourceInput)
    let nameCheck ← checkNames inputs fun names => (load names : IO _)
    unless nameCheck.refusals.isEmpty do
      unless expectedNameRefusal path nameCheck.refusals do
        failure s!"{stem}: the names do not resolve"
      continue
    let check := checkTyping (checkInstances nameCheck (files.map (·.toString))) (files.map (·.toString))
    if check.refusals.isEmpty then pass
    for refusal in check.refusals do failure s!"{stem}: {refusal.span.file}: {refusal.render}"
    checkPackages stem check
    let admitted := (check.packages.filter fun report => report.outcome matches .admitted _).size
    let checked := checkedFunctions check
    let (protocolRoots, protocols) := checkedProtocols check
    let typedOnly := (check.packages.filter fun report => report.outcome matches .typedOnly _).size
    let mut waits : Array String := #[]
    for report in check.packages do
      if let .waiting reason := report.outcome then
        unless waits.contains reason do waits := waits.push reason
    note s!"{stem}: {check.state.results.finished.size} function instances typed, {check.packages.size} packages, {admitted} admitted, {typedOnly} typed only{if waits.isEmpty then "" else s!", waiting for {", ".intercalate waits.toList}"}; {checked} functions in admitted packages; {protocolRoots} protocol roots admitted with {protocols} protocols checked; {check.state.results.obligations.size} obligations of laws"

/-- The generated program of the measurements: its bodies type. -/
def generatedTypingSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let text := Zkc.Tools.Frontend.Generate.program 50000
  let input : SourceInput := { name := "generated", parsed := parseString "generated" text }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  let check := checkTyping (checkInstances nameCheck #["generated"]) #["generated"]
  if check.refusals.isEmpty then pass
  for refusal in check.refusals.extract 0 5 do
    failure s!"the generated program: {refusal.span.file}: {refusal.render}"
  checkPackages "generated" check
  let admitted := (check.packages.filter fun report => report.outcome matches .admitted _).size
  let checked := checkedFunctions check
  note s!"generated program: {check.state.results.finished.size} function instances typed, {check.packages.size} packages, {admitted} admitted; {checked} functions in admitted packages"

/-- A body over a type of the vocabulary at a module argument is checked for its facts like any
other: the type has no form in a package yet, and the check of a definition does not wait for
it. -/
def moduleArgumentSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let text := "module held\nuse zkc::oracle::{table}\ndef with_oracle(xs: [nat], i: nat, h: Oracle<table<nat, 4>>) -> nat:\n    v = xs[i]\n    return v\n"
  let input : SourceInput := { name := "held", parsed := parseString "held" text }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  expectTrue nameCheck.refusals.isEmpty "a body over an oracle: the names resolve"
  let check := checkTyping (checkInstances nameCheck #["held"]) #["held"]
  match check.refusals[0]? with
  | some first =>
    expectTrue (first.rule == "TY7" && first.span.startLine.toNat == 4)
      s!"a body over an oracle: expected a refusal by TY7 at line 4; {first.render}"
  | none => failure "a body over an oracle: its facts are not checked"

end Zkc.Tests.Frontend
