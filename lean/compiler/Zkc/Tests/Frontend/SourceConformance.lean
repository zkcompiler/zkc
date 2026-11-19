import Zkc.Tests.Frontend.Reference
import Zkc.Frontend.Driver.SourcePhases

open Zkc.Frontend Zkc.Tests.Frontend

private def loadModule (repository : Repository) (segments : Array String) : TestM (Option SourceInput) := do
  let relative := "/".intercalate segments.toList ++ ".zkc"
  for directory in [repository.libraries, repository.examples / "support", repository.examples] do
    let file := directory / relative
    if ← file.pathExists then return some ⟨file.toString, Syntax.parse file.toString (← IO.FS.readBinFile file)⟩
  return none

/-- The corpus expects a final outcome. At the end of name resolution, a negative case
can still need typing or a later stage. Every early refusal must already match its rule. -/
private def checkNames (repository : Repository) : TestM Unit := do
  let contractCases := ["R-SX6c", "R-SX6d", "R-SX6e", "N-SX6a", "V-S6", "M-SCH3", "M-GKR4", "M-IPA4"]
  let mut checked := #[]
  let mut accepted := 0
  let mut early := 0
  let mut later := 0
  for path in ← sortedFiles repository.conformance "txt" do
    for block in readBlocks (← IO.FS.readFile path) do
      if block.expect.startsWith "skip" then continue
      let inputs := block.files.mapIdx fun i text =>
        let file := s!"{block.id}.{i}.zkc"
        ({ name := file, parsed := Syntax.parseString file text } : SourceInput)
      let assembly ← assemble inputs (loadModule repository)
      let assembled := (Driver.assemble assembly |>.runIn {vocabulary} {}).2
      let resolved := (Driver.resolve.runIn {vocabulary} assembled).2
      let errors := resolved.log.entries.filter (·.isError)
      let rules := refusalRules block.expect
      expectTrue (errors.all (rules.contains ·.rule))
        s!"{block.id}: expected `{block.expect}`, got {errors.map (·.rule)}"
      if contractCases.contains block.id && errors.any (fun d =>
          inputs.any (fun input => input.name == d.span.file) && rules.contains d.rule) then
        checked := checked.push block.id
      if rules.isEmpty then accepted := accepted + 1
      else if errors.isEmpty then later := later + 1
      else early := early + 1
  for id in contractCases do
    expectTrue (checked.contains id) s!"{id}: the contract error must be found before instantiation"
  note s!"Through name resolution: {accepted} positive cases, {early} early refusals, {later} negative cases left to later phases"

/-- SC1 and SP11 distinguish a scheme's deployment arguments from the goal's spec values. -/
private def checkSchemeArguments (repository : Repository) : TestM Unit := do
  let blocks := readBlocks (← IO.FS.readFile (repository.conformance / "layer-b.txt"))
  let some block := blocks.find? (·.id == "N-SC1a") | failure "missing N-SC1a"
  let some source := block.files[0]? | failure "empty N-SC1a"
  for (args, expected) in [("n = 8, e = 2", ["SP11"]), ("n = 8, spec e = 2", ["SC1"]), ("n = 8", [])] do
    let file := "scheme.zkc"
    let input := Syntax.parseString file (source.replace "n = 8, e = 2" args)
    let assembly := Id.run <| assemble #[⟨file, input⟩] fun _ => pure none
    let mut state : Compile.State := {}
    for phase in Driver.sourcePhases assembly do
      state := (phase.runIn {vocabulary} state).2
    let rules := (state.log.entries.filter (·.isError)).map (·.rule)
    expectTrue (rules.toList == expected) s!"N-SC1a with {args}: expected {expected}, got {rules}"

/-- Exercise the ordinary source pipeline and require admission of the named root,
or the precise refusal at body typing. A waiting body cannot satisfy a positive case. -/
private def checkProtocol (repository : Repository) (name root source : String)
    (refusal : Option String := none) : TestM Unit := do
  let input : SourceInput := ⟨name, Syntax.parseString name source⟩
  let assembly ← assemble #[input] (loadModule repository)
  let context := Typing.withProtocolBodies {vocabulary}
  let mut s : Compile.State := {}
  for phase in Driver.sourcePhases assembly do s := (phase.runIn context s).2
  s := (Typing.typeProgram.run context s).2
  let errors := s.log.entries.filter (·.isError)
  if let some rule := refusal then
    expectTrue (errors.map (·.rule) == #[rule]) s!"{name}: expected {rule}, got {errors.map (·.rule)}"
    return
  expectTrue errors.isEmpty s!"{name}: unexpected {errors.map (·.rule)}"
  let some (id, _) := s.results.roots.find? (fun (id, _) => Static.renderInstance s id == root)
    | failure s!"{name}: missing {root}"; return
  let .ok emission := Typing.emitRoot s id | failure s!"{name}: emission failed"; return
  expectTrue (emission.package ⟨[],[],[],[],[]⟩).checkEvidence.isOk s!"{name}: admission failed"

/-- These independent programs use facts about the current value. Change that
value or the required bound and the same pipeline must refuse the use. -/
private def checkCertifiedFacts (repository : Repository) : TestM Unit := do
  for (id, before, after_, rule) in [
      ("facts-mut-guard", "    return x", "    x := 8\n    return x", "TY8"),
      ("loop-mut-size-guard", "    return xs", "    xs := []\n    return xs", "TY5"),
      ("facts-no-commutativity-recovery", "xs[1 + i]", "xs[2 + i]", "TY7")] do
    let path := repository.conformance / "independent" / "cases" / id / "main.zkc"
    let source ← IO.FS.readFile path
    checkProtocol repository id "f" source
    checkProtocol repository (id ++ "-changed") "f" (source.replace before after_) (some rule)

/-- The same guard is useful only at its evaluating role. Include a lower bound
and a relation to an unknown index, which carry more information than an exact size. -/
private def checkSendFacts (repository : Repository) : TestM Unit := do
  let cases := readBlocks (← IO.FS.readFile (repository.conformance / "layer-a-types-facts.txt"))
  for (id, rule) in [("N-TY14e", none), ("V-H1", some "TY7"), ("I-4d", some "TY4"),
      ("V-F2", some "TY4")] do
    let some block := cases.find? (·.id == id) | failure s!"missing {id}"; continue
    let #[source] := block.files | failure s!"expected one source in {id}"; continue
    checkProtocol repository id "X" source rule
  for (id, rule) in [("wire-fact-does-not-cross", none), ("wire-fact-missing-receiver-guard", some "TY7"),
      ("wire-explicit-refinement", none)] do
    let source ← IO.FS.readFile (repository.conformance / "independent" / "cases" / id / "main.zkc")
    checkProtocol repository id "P" source rule
  let source (steps : List String) := String.intercalate "\n" <|
    ["module t", "protocol X roles(P,V,W)(xs:[nat] @P, ys:[nat] @P, k:nat @P):"] ++
    steps.map ("    " ++ ·)
  let send := "m <- send xs to V"
  let guarded := ["guard @P k < length(xs)", send]
  let loop := [send, "n @P = length(m)", "for i in 0..n:"]
  let bounded := ["guard @P length(xs) <= 8"] ++ loop
  let offset := ["guard @P length(xs) <= 8", send, "n @P = length(m)", "guard @P k <= n", "for i in k..n:"]
  for (name, steps, rule) in [
      ("index", guarded ++ ["z @P = m[k]"], none),
      ("second-send", guarded ++ ["n <- send m from P to V", "z @P = n[k]"], none),
      ("lower-bound", ["guard @P 7 < length(xs)", send, "z @P = m[3]"], none),
      ("different-subject", ["guard @P k < length(xs)", "m <- send ys to V", "z @P = m[k]"], some "TY7"),
      ("stronger-index", guarded ++ ["z @P = m[k + 1]"], some "TY7"),
      ("bounded-loop", bounded ++ ["    z @P = xs[i]"], none),
      ("other-loop-subject", bounded ++ ["    z @P = ys[i]"], some "TY7"),
      ("offset-loop", offset ++ ["    z @P = xs[i]"], none),
      ("offset-past-end", offset ++ ["    z @P = xs[i + 1]"], some "TY7"),
      ("unbounded-loop", loop ++ ["    guard @P i < n else refused"], some "CT4"),
      ("forward-after-guard", [send, "guard @V 3 < length(m)", "n <- send m from V to W", "z @V = n[3]"], none),
      ("forward-without-guard", ["guard @P 3 < length(xs)", send, "n <- send m from V to W", "z @V = n[3]"],
        some "TY7"),
      ("multicast-peer", ["m <- send xs to V, W", "guard @V 3 < length(m)", "z @W = m[3]"], some "TY7"),
      ("arm-local", ["if k < length(xs):", "    guard @P true", send, "z @P = m[k]"], some "TY7"),
      ("independent-receives", [send, "guard @V length(m) == 8", "n <- send xs to V", "z @V = n[7]"],
        some "TY7"),
      ("receiver-only", [send, "guard @V length(m) == 8", "z @P = m[7]"], some "TY7")
      ] do
    checkProtocol repository name "X" (source steps) rule

/-- Read the two SX7 tables as rendered. A missing, extra or reordered property, a
different audience, or a drift in stage or construction is observable here. -/
private def checkProperties (repository : Repository) : TestM Unit := do
  let table (file heading : String) : TestM (List String) := do
    let source ← IO.FS.readFile (repository.language / file)
    let some section_ := (source.splitOn heading)[1]? | return []
    return (((section_.splitOn "\n\n").head!.splitOn "\n").filter (·.startsWith "| `"))
  let catalog := Zkc.Security.properties.toList
  let actual ← table "CORE-LIBRARY.md" "| Property | Honest side | Clause it needs |"
  let expected := catalog.map fun p =>
    s!"| `{p.name}` | {p.honestSide.description} | {p.clause.description} | {", ".intercalate p.stages} | {", ".intercalate p.constructions} |"
  expectTrue (actual == expected) "security vocabulary rows differ from the Lean declarations"
  let clauses ← table "LANGUAGE.md" "| Property | Hypotheses | Conclusion |"
  expectTrue (clauses.map (fun row => (row.splitOn "`")[1]!) == catalog.map (·.name))
    "SX7 clause interpretations differ from the security vocabulary"

def main : IO Unit := do
  let repository : Repository := ⟨"../../language", "../../libraries", "../../examples"⟩
  let tally ← runSuite "Source conformance" do
    checkProperties repository
    checkCertifiedFacts repository
    checkSendFacts repository
    for (call, rule) in [
        ("Child(a, spec bound = a, spec bound = a)", some "SX4"),
        ("Child(a, spec bound = a; spec bound = a)", some "SX3"),
        ("Child(spec bound = a, a)", some "RM3"),
        ("Child(spec bound = a, a = a)", some "RM3"),
        ("Child(a, spec bound = a) @(P = P, P = V, V = V, V = P)", some "RM1"),
        ("Child(a, spec bound = a) @(P = V, P = P, V = P, V = V)", some "RM1"),
        ("Child(a, spec bound = a)", none)] do
      checkProtocol repository call "Caller" ("\n".intercalate [
        "module t", "protocol Child roles(P, V)(spec bound: bool, a: bool @P):",
        "    m <- send a to V", "protocol Caller roles(P, V)(a: bool @P):",
        "    " ++ call, ""]) rule
    corpusSuite repository
    conformanceSuite repository
    checkNames repository
    checkSchemeArguments repository
  if tally.failed > 0 then throw (IO.userError "source conformance failed")
