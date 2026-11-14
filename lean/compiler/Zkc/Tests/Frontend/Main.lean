import Zkc.Tests.Frontend

/-!
# The test driver of the package

`lake test` reads the language reference of the repository, `language/` (the directory that
holds `LANGUAGE.md`, `lib/`, `programs/` and `conformance/`), found from the directory of the
package. `lake test -- --reference <dir>`, or `ZKC_LANGUAGE_REFERENCE=<dir> lake test`, reads
another one. In a tree without a reference the driver stops with an error, unless
`--without-reference` is given, which runs the tests that need no reference only. The
independent conformance suite is `conformance/independent/` of the repository's reference;
`--independent <dir>`, or `ZKC_INDEPENDENT_CONFORMANCE=<dir>`, names another one, and without
either the suite is skipped, and the driver says so.

`--baseline <dir>`, or `ZKC_DIFFERENTIAL_BASELINE=<dir>`, also compares every program of the
corpus with the baseline in that directory by runs (`DifferentialRuns`), with the reference;
`--compare-by-runs` runs packages also when their text is the baseline's, `--every-root` runs
every root of the generated program where it is otherwise sampled, `--uninterpreted` runs under
the provider of uninterpreted rows, and `--mutants` gives the mutant score. Without a baseline the comparison is skipped, and the driver says so.
`--write-baseline <dir>` writes the baseline of the corpus there and runs no test.
-/

open Zkc.Tests.Frontend

def usage : String :=
  "usage: zkc-frontend-tests [--reference <dir> | --without-reference] [--independent <dir>]
       [--baseline <dir> [--compare-by-runs] [--every-root] [--uninterpreted] [--mutants] | --write-baseline <dir>
        | --trees [--probes <dir>] [--arithmetic]]
without --reference the reference is the one that the variable ZKC_LANGUAGE_REFERENCE names,
or else the directory language/ of the repository; the directory of the independent
conformance suite may also be given by ZKC_INDEPENDENT_CONFORMANCE, and the baseline of the
differential runs by ZKC_DIFFERENTIAL_BASELINE"

/-- The options of the driver. -/
structure DriverOptions where
  /-- The reference: `some none` without it. -/
  reference : Option (Option String) := none
  independent : Option String := none
  baseline : Option String := none
  writeBaseline : Option String := none
  byRuns : Bool := false
  everyRoot : Bool := false
  mutants : Bool := false
  uninterpreted : Bool := false
  /-- Only the suite of the typed trees of protocols: their invariants and the second reading. -/
  trees : Bool := false
  /-- With `--trees`: a directory of probes, each a `.zkc` file one directory below it. -/
  probes : Option String := none
  /-- With `--trees`: the second reading also under the model that computes the rows. -/
  arithmetic : Bool := false

def readDriverOptions : List String → DriverOptions → Option DriverOptions
  | "--reference" :: dir :: rest, options => readDriverOptions rest { options with reference := some (some dir) }
  | "--without-reference" :: rest, options => readDriverOptions rest { options with reference := some none }
  | "--independent" :: dir :: rest, options => readDriverOptions rest { options with independent := some dir }
  | "--baseline" :: dir :: rest, options => readDriverOptions rest { options with baseline := some dir }
  | "--write-baseline" :: dir :: rest, options =>
    readDriverOptions rest { options with writeBaseline := some dir }
  | "--compare-by-runs" :: rest, options => readDriverOptions rest { options with byRuns := true }
  | "--every-root" :: rest, options => readDriverOptions rest { options with everyRoot := true }
  | "--mutants" :: rest, options => readDriverOptions rest { options with mutants := true }
  | "--trees" :: rest, options => readDriverOptions rest { options with trees := true }
  | "--probes" :: dir :: rest, options => readDriverOptions rest { options with probes := some dir }
  | "--arithmetic" :: rest, options => readDriverOptions rest { options with arithmetic := true }
  | "--uninterpreted" :: rest, options =>
    readDriverOptions rest { options with uninterpreted := true }
  | [], options => some options
  | _, _ => none

/-- The language reference of the repository, from the directory of the package, when the
package is in the repository; and the independent conformance suite inside it. -/
def repositoryReference : IO (Option String × Option String) := do
  let reference : System.FilePath := "../../language"
  unless ← (reference / "conformance").isDir do return (none, none)
  let independent := reference / "conformance" / "independent"
  let hasIndependent ← (independent / "expectations.json").pathExists
  return (some reference.toString, if hasIndependent then some independent.toString else none)

def main (args : List String) : IO UInt32 := do
  let (inRepository, independentInRepository) ← repositoryReference
  let fromEnvironment := (← IO.getEnv "ZKC_LANGUAGE_REFERENCE").orElse fun _ => inRepository
  let independentFromEnvironment :=
    (← IO.getEnv "ZKC_INDEPENDENT_CONFORMANCE").orElse fun _ => independentInRepository
  let baselineFromEnvironment ← IO.getEnv "ZKC_DIFFERENTIAL_BASELINE"
  let some options := readDriverOptions args {}
    | IO.eprintln usage
      return 2
  let some reference := options.reference.orElse fun _ => fromEnvironment.map some
    | IO.eprintln usage
      return 2
  let independent := options.independent.orElse fun _ => independentFromEnvironment
  if let some directory := options.writeBaseline then
    let some reference := reference
      | IO.eprintln "--write-baseline needs the reference"
        return 2
    return ← writeCorpusBaseline directory reference (independent.map (·))
  let baseline := options.baseline.orElse fun _ => baselineFromEnvironment
  if options.trees then
    let some reference := reference
      | IO.eprintln "--trees needs the reference"
        return 2
    let tally ← runSuite "typed trees of protocols" (treeSuite reference (independent.map (·)) (options.probes.map (·)) options.arithmetic)
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
  tallies := tallies.push (← runSuite "differential runs: coins by the source" keyingSuite)
  tallies := tallies.push (← runSuite "differential runs: mutants by reach" reachSuite)
  tallies := tallies.push (← runSuite "schemes" schemeSuite)
  tallies := tallies.push (← runSuite "session" sessionSuite)
  match reference with
  | some dir =>
    let path : System.FilePath := dir
    unless ← (path / "conformance").isDir do
      IO.eprintln s!"{dir} is not the reference directory: it has no conformance/"
      return 2
    tallies := tallies.push (← runSuite "lib/ and programs/" (corpusSuite path))
    tallies := tallies.push (← runSuite "conformance" (conformanceSuite path))
    tallies := tallies.push (← runSuite "names: conformance of layer A" (conformanceNamesSuite path))
    tallies := tallies.push (← runSuite "names: lib/" (libraryNamesSuite path))
    tallies := tallies.push (← runSuite "names: programs/" (programNamesSuite path))
    tallies := tallies.push (← runSuite "names: generated program" (generatedNamesSuite path))
    tallies := tallies.push (← runSuite "instances: conformance of layer A" (conformanceInstancesSuite path))
    tallies := tallies.push (← runSuite "instances: lib/" (libraryInstancesSuite path))
    tallies := tallies.push (← runSuite "instances: programs/" (programInstancesSuite path))
    tallies := tallies.push (← runSuite "instances: generated program" (generatedInstancesSuite path))
    tallies := tallies.push (← runSuite "instances: a `where` that waits" (waitingInstanceSuite path))
    tallies := tallies.push (← runSuite "typing: conformance of layer A" (conformanceTypingSuite path))
    tallies := tallies.push (← runSuite "typing: lib/" (libraryTypingSuite path))
    tallies := tallies.push (← runSuite "typing: a body over a module argument" (moduleArgumentSuite path))
    tallies := tallies.push (← runSuite "typing: programs/" (programTypingSuite path))
    tallies := tallies.push (← runSuite "typing: generated program" (generatedTypingSuite path))
    tallies := tallies.push (← runSuite "running: zkc::sequence" (sequenceRunSuite path))
    tallies := tallies.push (← runSuite "running: members of the sorts" (membersRunSuite path))
    tallies := tallies.push (← runSuite "running: protocols of programs/" (referenceProtocolSuite path))
    tallies := tallies.push (← runSuite "running: Sumcheck" (sumcheckRunSuite path))
    tallies := tallies.push (← runSuite "running: true statements" (generatorSuite path))
    tallies := tallies.push (← runSuite "schemes: the derived Schnorr scheme" (derivedSchnorrSuite path))
    tallies := tallies.push (← runSuite "schemes: programs/" (referenceSchemeSuite path))
  | none => IO.println "the tests of the reference were not run (--without-reference)"
  match independent with
  | some dir =>
    let path : System.FilePath := dir
    unless ← (path / "expectations.json").pathExists do
      IO.eprintln s!"{dir} is not the independent conformance suite: it has no expectations.json"
      return 2
    -- the cases are checked with the library of the reference
    match reference with
    | some reference =>
      tallies := tallies.push (← runSuite "independent conformance"
        (independentSuite path ((reference : System.FilePath) / "lib")))
    | none => IO.println "the independent conformance suite was not run (it needs the reference)"
  | none => IO.println "the independent conformance suite was not run (no suite was found or given)"
  match baseline, reference with
  | some directory, some reference =>
    let options : DifferentialOptions := { baseline := directory, byRuns := options.byRuns
                                           everyRoot := options.everyRoot
                                           mutants := options.mutants
                                           uninterpreted := options.uninterpreted }
    tallies := tallies.push (← runSuite "differential runs" (differentialSuite options reference
      (independent.map (·))))
  | some _, none => IO.println "the differential runs were not run (they need the reference)"
  | none, _ => IO.println "the differential runs were not run (no --baseline)"
  let passed := tallies.foldl (· + ·.passed) 0
  let failed := tallies.foldl (· + ·.failed) 0
  IO.println s!"total: {passed} checks passed, {failed} failed"
  return if failed == 0 then 0 else 1
