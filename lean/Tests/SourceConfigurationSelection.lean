module

public import Tests.Generators.SourceConfigurations.Counter
public import ZkcTools.StructuredSource.Bindings.Inputs
meta import Tests.Generators.SourceConfigurations.Counter
meta import ZkcTools.StructuredSource.Bindings.Inputs
meta import ZkcTools.StructuredSource.Bindings.SourceInstallation

@[expose] public section

set_option autoImplicit false

namespace Tests.SourceConfigurationSelection
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Bindings
open Tests.Generators.SourceConfigurations.Counter

def require {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def expect (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw (IO.userError reason)

def refuses {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error found => expect (found == reason) ("unexpected refusal: " ++ found)
  | .ok _ => throw (IO.userError ("expected refusal: " ++ reason))

def changedSnapshot (stop : Bool) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
      | .function function => if function.name == bridge.name then
          .function { function with body :=
            if stop then (Block.block [.instruction (.apply "reorder") [1, 0] [.boolean, .index] [] "reorder"]
              (.stop .reject "stopped"))
            else (Block.block [.instruction (.apply "reorder") [1, 0] [.boolean, .index] [] "reorder"] (.ret [0, 4, 1])) }
        else .function function
      | definition => definition }

def duplicateSnapshot : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
      | .function function => if function.name == root.name then
          .function { function with body := match function.body with
            | .block [instruction@(.instruction descriptor _ results regions _)] terminator =>
                let regions := regions.map fun
                  | .region inputs outputs (.block instructions terminator) =>
                    .region inputs outputs (.block (instructions.map fun
                      | .instruction descriptor operands results regions site =>
                          .instruction descriptor operands results regions (site ++ "More")) terminator)
                .block [instruction, .instruction descriptor [3, 4, 5, 6, 7] results regions "more"] terminator
            | body => body }
        else .function function
      | definition => definition }

/-- A repeat with no captures still retains its complete continuation frame.
Its resume function has no need to inspect that frame. -/
def noCaptureSnapshot : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
      | .function function => if function.name == root.name then
          .function { function with
            inputs := .index :: state
            interface := some ⟨["Auditor"], ports 4, ports 3⟩
            body := .block [
              .instruction (.protocolRepeat 3 5 ["Auditor"] (ports 3)) [0, 1, 2, 3] state
                [.region (.index :: state) state (.block [
                  .instruction (.localCall "route" "Auditor") [1, 2, 3] state [] "prepare",
                  .instruction (.protocolApply "visit" ["Auditor"]) [0, 1, 2] state [] "visit",
                  .instruction (.protocolApply "visit" ["Auditor"]) [0, 1, 2] state [] "finish"
                ] (.yield [0, 1, 2]))] "passes"] (.ret [0, 1, 2]) }
        else .function function
      | definition => definition }

def run : IO Unit := do
  let program ← require (check snapshot)
  let installed ← require (configure program)
  expect (installed.associations.map Prod.fst == ["route", "reorder"]) "configuration helper names"
  expect (installed.protocols.length == 2) "configuration protocols"
  refuses (uniqueHelper program .local [.index, .boolean] [.boolean, .index])
    "helper-association-ambiguous-or-missing"
  refuses (uniqueHelper program .math [] [.boolean]) "helper-association-ambiguous-or-missing"
  refuses (uniqueHelperWhere program fun _ => false) "helper-association-ambiguous-or-missing"
  refuses (uniqueCandidate "ambiguous" [1, 1]) "ambiguous"
  refuses (uniqueProtocol program ⟨"counter::Counter", [("Limit", .natural "4")]⟩)
    "source-protocol-ambiguous-or-missing"
  let childIndex ← require (uniqueProtocol program ⟨"counter::Visit", []⟩)
  let rootIndex ← require (uniqueProtocol program ⟨"counter::Counter", [("Limit", .natural "5")]⟩)
  let some child := program.payload.protocols[childIndex]? | throw (IO.userError "child index")
  let (selected, site) ← require (callbackCalling program rootIndex 0 child.signature)
  expect (site == "visit") "call selected by signature, independent of label"
  refuses (callbackCalling program rootIndex 1 child.signature) "source-role-index"
  refuses (callbackCalling program rootIndex 0 child.signature 1)
    "source-callback-call-ambiguous-or-missing"
  refuses (callbackCalling program rootIndex 0 { child.signature with outputs := [.boolean] })
    "source-callback-call-ambiguous-or-missing"
  refuses (uniqueCallback program rootIndex fun _ => false) "source-callback-ambiguous-or-missing"
  refuses (uniqueCallback program 999 fun _ => true) "source-protocol-index"
  let duplicate ← require (check duplicateSnapshot)
  refuses (callbackCalling duplicate (← require (uniqueProtocol duplicate
    ⟨"counter::Counter", [("Limit", .natural "5")]⟩)) 0 child.signature)
    "source-callback-call-ambiguous-or-missing"
  refuses (uniqueCallback duplicate rootIndex fun _ => true) "source-callback-ambiguous-or-missing"
  refuses (callbackCallSource program selected site [0] 1 "call" "loop") "source-call-alias-role"
  refuses (callbackCallSource program selected "missing" [0] 0 "call" "loop") "bindings-linear-call-required"
  refuses (helperBodySource program "missing" 999) "helper-association-index"
  refuses (helperAliasSource program "missing" 999) "helper-association-index"
  refuses (helperTemplateSource program "missing" 999) "helper-association-index"
  let halted : Form [] [] [] [] := .halt .reject
  expect (prefixApplication halted |>.isNone) "stopped prefix has no selected call"
  refuses (afterRepeatHelpers halted) "source-linear-repeat-required"
  let receiving : Form [] [] [] [] := .receive .index "event" 0 (.halt .reject)
  expect (prefixApplication receiving |>.isNone) "effects are not skipped during call selection"
  refuses (afterRepeatHelpers receiving) "source-linear-repeat-required"
  -- Both mutations are admitted and selectable. Only the full-body equation
  -- can reject their association with the original, independently owned template.
  for stop in [false, true] do
    let changed ← require (check (changedSnapshot stop))
    let changedInstalled ← require (configure changed)
    let oldTemplates ← require (helperTemplatesSource program installed.templates installed.associations)
    let newTemplates ← require (helperTemplatesSource changed changedInstalled.templates changedInstalled.associations)
    expect (oldTemplates != newTemplates) "full-body template retains changed returns/stops"
  let reordered ← require (check { snapshot with definitions := snapshot.definitions.reverse })
  let reorderedInstalled ← require (configure reordered)
  expect (reorderedInstalled.associations.map Prod.fst == installed.associations.map Prod.fst)
    "reordered declarations select same client roles"
  IO.println "source configuration selection/refusal controls passed"

def output : Output := {
  moduleName := "CounterBindings"
  sourceModule := "CounterInputs"
  programExpression := "CounterInputs.program"
  importedExpression := "CounterInputs.imported" }

/-- Generate only into the supplied scratch tree. Compile the resulting inputs,
bindings, callbacks, templates, associations and caller as a focused kernel gate. -/
def generate (directory : System.FilePath) (withoutCaptures : Bool := false) : IO Unit := do
  let program ← require (check (if withoutCaptures then noCaptureSnapshot else snapshot))
  let installed ← require (configure program)
  let output := { output with protocols := installed.protocols }
  let destination := directory
  IO.FS.createDirAll destination
  IO.FS.writeFile (destination / "CounterInputs.lean")
    (inputsSource program output.sourceModule "Tests.SourceConfigurationSelection" output.sourceModule
      (if withoutCaptures then "Tests.SourceConfigurationSelection.noCaptureSnapshot"
       else "Tests.Generators.SourceConfigurations.Counter.snapshot"))
  IO.FS.writeFile (destination / "CounterBindings.lean") (← require (source program output))
  IO.FS.writeFile (destination / "CounterBindingsCallbacks.lean") (← require (callbacksSource program output))
  IO.FS.writeFile (destination / "CounterTemplates.lean")
    (← require (helperTemplatesSource program installed.templates installed.associations))
  IO.FS.writeFile (destination / "CounterBindingsHelpers.lean")
    (← require (helperAssociationsSource program output installed.templates installed.namespaceSuffix installed.associations))
  IO.FS.writeFile (destination / "CounterBindingsCaller.lean") (← require (installed.callerSource output))
  -- Compile these two files expecting a body-association error. They have the
  -- original templates but a different admitted payload; names/ABIs still match.
  for (suffix, stop) in [("Swapped", false), ("Stopped", true)] do
    let changed ← require (check (changedSnapshot stop))
    let changedInstalled ← require (configure changed)
    let inputModule := "Counter" ++ suffix ++ "Inputs"
    let literal := inputsSource changed inputModule "Tests.SourceConfigurationSelection" inputModule
      ("(Tests.SourceConfigurationSelection.changedSnapshot " ++ toString stop ++ ")")
    IO.FS.writeFile (destination / ("Counter" ++ suffix ++ "Inputs.lean")) literal
    let associationOutput := { output with
      moduleName := "Counter" ++ suffix }
    let association ← require (helperAssociationsSource changed associationOutput installed.templates
      installed.namespaceSuffix changedInstalled.associations)
    let association := association.replace ("public import " ++ associationOutput.moduleName ++ "Callbacks")
      ("public import " ++ associationOutput.moduleName ++ "Inputs")
    let association := association.replace ("open " ++ associationOutput.moduleName ++ "\n")
      ("open " ++ associationOutput.moduleName ++ "Inputs\n" ++
        "noncomputable abbrev payload := program.payload\n")
    IO.FS.writeFile (destination / ("Counter" ++ suffix ++ "Helpers.lean")) association
  IO.println "generated domain-free source configuration fixture and stale-template controls"

end Tests.SourceConfigurationSelection

def Tests.SourceConfigurationSelection.checkGenerated (args : List String) : IO Unit := do
  Tests.SourceConfigurationSelection.run
  let [directory] := args | throw (IO.userError "expected scratch output directory")
  let directory := System.FilePath.mk directory
  IO.FS.createDirAll directory
  let directory ← IO.FS.realPath directory
  for withoutCaptures in [false, true] do
    let directory := directory / (if withoutCaptures then "without-captures" else "with-captures")
    IO.FS.createDirAll directory
    Tests.SourceConfigurationSelection.generate directory withoutCaptures
    let leanPath := directory.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""
    let compile := fun (name : String) => IO.Process.output {
      cmd := "lean"
      args := #["-j2", "-R", directory.toString, "-DwarningAsError=true", "-DautoImplicit=false",
        "-o", (directory / (name ++ ".olean")).toString, (directory / (name ++ ".lean")).toString]
      env := #[("LEAN_PATH", some leanPath)] }
    for name in ["CounterInputs", "CounterBindings", "CounterBindingsCallbacks", "CounterTemplates",
        "CounterBindingsHelpers", "CounterBindingsCaller", "CounterSwappedInputs", "CounterStoppedInputs"] do
      let result ← compile name
      IO.FS.writeFile (directory / (name ++ ".log")) (result.stdout ++ result.stderr)
      unless result.exitCode == 0 do
        throw (IO.userError ("generated source configuration failed: " ++ name ++ "\n" ++ result.stdout ++ result.stderr))
    for name in ["CounterSwappedHelpers", "CounterStoppedHelpers"] do
      let result ← compile name
      let log := result.stdout ++ result.stderr
      IO.FS.writeFile (directory / (name ++ ".log")) log
      unless result.exitCode != 0 && (log.splitOn ": error").length == 2 &&
          (log.splitOn "error: Application type mismatch").length == 2 &&
          (log.splitOn "routeDefinition.raw = routeBody.erase").length == 2 do
        throw (IO.userError ("stale template did not fail at its body equation: " ++ name ++ "\n" ++ log))
    IO.println "source configuration: 8 generated modules checked; swapped/stopped full-body associations refused"

end
