import Zkc.Tests.Frontend

/-!
# The test driver of the package

`lake test` reads the repository from the directory of the package: the reference of the
language and its conformance tests in `../../language`, the library in source in
`../../libraries` and the worked programs in `../../examples`. A missing directory stops the
driver with an error. `lake test -- --trees` runs only the suite of the typed trees of
protocols: their invariants and the second reading.
-/

open Zkc.Tests.Frontend

def usage : String :=
  "usage: zkc-frontend-tests [--trees]
the driver reads ../../language, ../../libraries and ../../examples from the directory of the package"

/-- The directories of the repository, from the directory of the package. -/
def repository : Repository :=
  { language := "../../language", libraries := "../../libraries", examples := "../../examples" }

/-- What the driver reads that is missing, each as a line. -/
def missingInputs (repository : Repository) : IO (Array String) := do
  let mut missing := #[]
  for (path, what) in [(repository.language / "LANGUAGE.md", "the reference of the language"),
      (repository.conformance, "the conformance tests"),
      (repository.independent / "expectations.json", "the independent conformance suite"),
      (repository.libraries, "the library in source"),
      (repository.examples, "the worked programs"),
      (("scripts" : System.FilePath) / "replay_derived_schnorr.py", "the independent replay of the derived Schnorr proof")] do
    unless ← path.pathExists do missing := missing.push s!"{path} is not found: {what}"
  return missing

def main (args : List String) : IO UInt32 := do
  let trees ← match args with
    | [] => pure false
    | ["--trees"] => pure true
    | _ => do
      IO.eprintln usage
      return 2
  let missing ← missingInputs repository
  unless missing.isEmpty do
    for line in missing do IO.eprintln line
    return 2
  if trees then
    let tally ← runSuite "typed trees of protocols" (treeSuite repository)
    return if tally.failed == 0 then 0 else 1
  let mut tallies := #[]
  tallies := tallies.push (← runSuite "rules of §3 and §5" ruleCaseSuite)
  tallies := tallies.push (← runSuite "contextual words" contextualWordSuite)
  tallies := tallies.push (← runSuite "bytes" byteSuite)
  tallies := tallies.push (← runSuite "precedence" precedenceSuite)
  tallies := tallies.push (← runSuite "spellings" spellingSuite)
  tallies := tallies.push (← runSuite "printer" printerSuite)
  tallies := tallies.push (← runSuite "generated program" generatedSuite)
  tallies := tallies.push (← runSuite "names" nameCaseSuite)
  tallies := tallies.push (← runSuite "instances" instanceCaseSuite)
  tallies := tallies.push (← runSuite "typing" typingCaseSuite)
  tallies := tallies.push (← runSuite "running" runningSuite)
  tallies := tallies.push (← runSuite "running: opaque typing" opaqueRunSuite)
  tallies := tallies.push (← runSuite "protocols" protocolCaseSuite)
  tallies := tallies.push (← runSuite "running: protocols" protocolRunSuite)
  tallies := tallies.push (← runSuite "running: protocol constructs" protocolRunTests)
  tallies := tallies.push (← runSuite "running: the keys of coins" keyingSuite)
  tallies := tallies.push (← runSuite "schemes" schemeSuite)
  tallies := tallies.push (← runSuite "session" sessionSuite)
  tallies := tallies.push (← runSuite "libraries/ and examples/" (corpusSuite repository))
  tallies := tallies.push (← runSuite "formatting keeps a program" (formatCaseSuite repository))
  tallies := tallies.push (← runSuite "formatting keeps a program: libraries/ and examples/"
    (corpusFormattingSuite repository))
  tallies := tallies.push (← runSuite "conformance" (conformanceSuite repository))
  tallies := tallies.push (← runSuite "names: conformance of layer A" (conformanceNamesSuite repository))
  tallies := tallies.push (← runSuite "names: libraries/" (libraryNamesSuite repository))
  tallies := tallies.push (← runSuite "names: examples/" (programNamesSuite repository))
  tallies := tallies.push (← runSuite "names: generated program" (generatedNamesSuite repository))
  tallies := tallies.push (← runSuite "instances: conformance of layer A" (conformanceInstancesSuite repository))
  tallies := tallies.push (← runSuite "instances: libraries/" (libraryInstancesSuite repository))
  tallies := tallies.push (← runSuite "instances: examples/" (programInstancesSuite repository))
  tallies := tallies.push (← runSuite "instances: generated program" (generatedInstancesSuite repository))
  tallies := tallies.push (← runSuite "instances: a `where` that waits" (waitingInstanceSuite repository))
  tallies := tallies.push (← runSuite "typing: conformance of layer A" (conformanceTypingSuite repository))
  tallies := tallies.push (← runSuite "typing: libraries/" (libraryTypingSuite repository))
  tallies := tallies.push (← runSuite "typing: a body over a module argument" (moduleArgumentSuite repository))
  tallies := tallies.push (← runSuite "typing: examples/" (programTypingSuite repository))
  tallies := tallies.push (← runSuite "typing: generated program" (generatedTypingSuite repository))
  tallies := tallies.push (← runSuite "running: zkc::sequence" (sequenceRunSuite repository))
  tallies := tallies.push (← runSuite "running: members of the sorts" (membersRunSuite repository))
  tallies := tallies.push (← runSuite "running: protocols of examples/" (referenceProtocolSuite repository))
  tallies := tallies.push (← runSuite "running: Sumcheck" (sumcheckRunSuite repository))
  tallies := tallies.push (← runSuite "running: true statements" (generatorSuite repository))
  tallies := tallies.push (← runSuite "schemes: the derived Schnorr scheme" (derivedSchnorrSuite repository))
  tallies := tallies.push (← runSuite "schemes: examples/" (referenceSchemeSuite repository))
  -- the cases are checked with the library in source
  tallies := tallies.push (← runSuite "independent conformance"
    (independentSuite repository.independent repository.libraries))
  let passed := tallies.foldl (· + ·.passed) 0
  let failed := tallies.foldl (· + ·.failed) 0
  IO.println s!"total: {passed} checks passed, {failed} failed"
  return if failed == 0 then 0 else 1
