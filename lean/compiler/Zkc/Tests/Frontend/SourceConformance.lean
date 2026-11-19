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

/-- These independent programs use facts about the current value. Change that
value or the required bound and the same pipeline must refuse the use. -/
private def checkCertifiedFacts (repository : Repository) : TestM Unit := do
  for (id, before, after_, rule) in [
      ("facts-mut-guard", "    return x", "    x := 8\n    return x", "TY8"),
      ("loop-mut-size-guard", "    return xs", "    xs := []\n    return xs", "TY5"),
      ("facts-no-commutativity-recovery", "xs[1 + i]", "xs[2 + i]", "TY7")] do
    let path := repository.conformance / "independent" / "cases" / id / "main.zkc"
    let source ← IO.FS.readFile path
    for (program, valid) in [(source, true), (source.replace before after_, false)] do
      let input : SourceInput := ⟨path.toString, Syntax.parseString path.toString program⟩
      let assembly ← assemble #[input] (loadModule repository)
      let context := Typing.withProtocolBodies {vocabulary}
      let mut s : Compile.State := {}
      for phase in Driver.sourcePhases assembly do s := (phase.runIn context s).2
      s := (Typing.typeProgram.run context s).2
      if valid then
        let #[(root, _)] := s.results.roots | failure s!"{id}: expected one function root"; continue
        let .ok emission := Typing.emitRoot s root | failure s!"{id}: emission failed"; continue
        expectTrue (emission.package ⟨[],[],[],[],[]⟩).checkEvidence.isOk s!"{id}: admission failed"
      else
        expectTrue (s.log.entries.any fun d => d.isError && d.rule == rule) s!"{id}: expected {rule}"

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
    corpusSuite repository
    conformanceSuite repository
    checkNames repository
    checkSchemeArguments repository
  if tally.failed > 0 then throw (IO.userError "source conformance failed")
