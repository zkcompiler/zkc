import Zkc.Tests.Frontend
import Zkc.Tools.Audit
import Zkc.Tools.Frontend

/-!
# Source language tests

The driver checks source programs against the language tables, libraries and worked examples.
-/

open Zkc.Tests.Frontend

def usage : String :=
  "usage: zkc-frontend-tests
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
      (repository.examples, "the worked programs")] do
    unless ← path.pathExists do missing := missing.push s!"{path} is not found: {what}"
  return missing

/-- A frontend library imports all its modules except the independently invoked commands
and checks. Those define separate Lean declarations named `main`. -/
def checkLibraryImports : IO Unit := do
  let libraries : Array (Lean.Name × Array Lean.Name) := #[
    (`Zkc.Frontend, #[]),
    (`Zkc.Tools.Frontend, #[`Zkc.Tools.Frontend.Main, `Zkc.Tools.Frontend.CheckMain]),
    (`Zkc.Tests.Frontend, #[`Zkc.Tests.Frontend.Main, `Zkc.Tests.Frontend.SourceConformance,
      `Zkc.Tests.Frontend.ProtocolViews, `Zkc.Tests.Frontend.PrintedPackages])]
  Lean.initSearchPath (← Lean.findSysroot) [".lake/build/lib/lean"]
  let imports := libraries.map fun (root, _) => ({module := root} : Lean.Import)
  let env ← Lean.importModules imports {} (loadExts := false) (level := .private)
  for (root, commands) in libraries do
    let imported := Zkc.Tools.Audit.importClosure env #[root]
    for file in ← Zkc.Tools.Audit.libraryFiles "." root do
      unless imported.contains file || commands.contains file do
        throw (IO.userError s!"{root} does not import {file}")

def knownFailures : List KnownFailure := []

def frontendSuites : List (String × TestM Unit) := [
  ("rules of §3 and §5", ruleCaseSuite),
  ("contextual words", contextualWordSuite),
  ("bytes", byteSuite),
  ("precedence", precedenceSuite),
  ("spellings", spellingSuite),
  ("printer", printerSuite),
  ("generated program", generatedSuite),
  ("names", nameCaseSuite),
  ("instances", instanceCaseSuite),
  ("typing", typingCaseSuite),
  ("written statements for primitive bindings", writtenPrimitiveSuite),
  ("session", sessionSuite),
  ("libraries/ and examples/", corpusSuite repository),
  ("formatting keeps a program", formatCaseSuite repository),
  ("formatting keeps a program: libraries/ and examples/", corpusFormattingSuite repository),
  ("formatting keeps a program: conformance tests tagged `fmt`", formatTaggedSuite repository),
  ("formatting keeps a program: independent conformance", independentFormattingSuite repository),
  ("conformance", conformanceSuite repository),
  ("names: conformance of layer A", conformanceNamesSuite repository),
  ("names: libraries/", libraryNamesSuite repository),
  ("names: examples/", programNamesSuite repository),
  ("names: generated program", generatedNamesSuite repository),
  ("instances: conformance of layer A", conformanceInstancesSuite repository),
  ("instances: libraries/", libraryInstancesSuite repository),
  ("instances: examples/", programInstancesSuite repository),
  ("instances: generated program", generatedInstancesSuite repository),
  ("instances: a `where` that waits", waitingInstanceSuite repository),
  ("typing: conformance of layer A", conformanceTypingSuite repository),
  ("typing: libraries/", libraryTypingSuite repository),
  ("typing: pairing member", pairingMemberSuite repository),
  ("typing: module formation", memberFormationSuite repository),
  ("typing: open protocol heads", openProtocolHeadsSuite repository),
  ("typing: member parameters", memberParameterSuite),
  ("typing: module depth", moduleDepthSuite),
  ("typing: module checks across phases", phasedModuleChecksSuite),
  ("typing: default member roots", defaultMemberRootsSuite),
  ("typing: package layout of defaults", defaultPackageLayoutSuite),
  ("typing: module observations", moduleObservationsSuite),
  ("written: module selection", writtenSelectionReadsSuite repository),
  ("typing: module member rows", memberRowSuite repository),
  ("typing: a body over a module argument", moduleArgumentSuite repository),
  ("typing: examples/", programTypingSuite repository),
  ("typing: generated program", generatedTypingSuite repository),
  ("independent conformance", independentSuite repository.independent repository.libraries)]

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln usage
    return 2
  let missing ← missingInputs repository
  unless missing.isEmpty do
    for line in missing do IO.eprintln line
    return 2
  checkLibraryImports
  ProtocolEmission.check "../.."
  let counts ← runSuites frontendSuites knownFailures
  IO.println s!"total: {counts.passed} checks passed, {counts.known} known failures, {counts.failed} failed"
  return if counts.failed == 0 then 0 else 1
