module

public import ZkcTools.StructuredSource.Bindings.Callbacks
public import ZkcTools.StructuredSource.Bindings.RoleViews
public import Tests.StructuredBindingsGeneric
meta import Tests.StructuredBindingsGeneric
meta import ZkcTools.StructuredSource.Bindings.Callbacks
meta import ZkcTools.StructuredSource.Bindings.RoleViews

@[expose] public section

set_option autoImplicit false
namespace Tests.RepeatOccurrences
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings

def spec : RepeatSpec := ⟨[.index, .index], [.index], [0, 1], [[0], [0, 1]], 4⟩

def arguments : Operands [.index, .index, .index, .index]
    (.index :: (spec.state ++ spec.captures)) :=
  .cons .here (.cons (.there .here) (.cons (.there (.there .here))
    (.cons (.there (.there (.there .here))) .nil)))

/-- Both results matter; the second result deliberately reads a capture. -/
def callback : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state :=
  .ret (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))

def original : RepeatSite :=
  ⟨_, _, spec, "same", arguments, callback, .ret (.cons .here (.cons (.there .here) .nil))⟩

def nestedCallback : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state :=
  .letOp (.repeat spec "same") arguments (.cons callback .nil)
    (.ret (.cons .here (.cons (.there .here) .nil)))

def nested : Region protocolDialect original.context original.outputs :=
  .letOp (.repeat spec "same") arguments (.cons nestedCallback .nil)
    (.bind (.stop (out := []) .refused)
      (.letOp (.repeat spec "same")
        (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
          (.cons (.there (.there (.there .here))) .nil))))
        (.cons (.stop .reject) .nil) (.stop .refused)))

example : (repeatSites nested).map (·.site) = ["same", "same", "same"] := rfl
example : (repeatInventory nested).map (·.position) = [[], [0], [1, 1]] := rfl
example : (selectRepeat 3 nested) = none := rfl
example : selectRepeat 0 (.stop .reject : Region protocolDialect [] []) = none := rfl
example : selectRepeat 0 (.ret .nil : Region protocolDialect [] []) = none := rfl

/-- Independent evidence, rather than a Boolean inspector success. -/
def inner : RepeatAt original nested := .repeatBody _ _ _ _ _ .here
example : (⟨original, inner⟩ : RepeatOccurrence nested) ∈ repeatInventory nested :=
  repeatInventory_complete _
example : inner.position = [0] := rfl
example : inner.enclosing.map (fun (path, site) => (path, site.spec.stateScopes)) =
    [([], [[0], [0, 1]])] := rfl
example : inner.enclosing.map (fun (_, site) => site.operands.indices) = [[0, 1, 2, 3]] := rfl

def selectedInner : RepeatAt original nested := selectedRepeat (ordinal := 1) (by kernel_rfl)
example : selectedInner.position = [0] := by kernel_rfl

/-- The suffix after a stop is lexical source, not an executed occurrence. -/
example : ((selectRepeat 2 nested).map (·.position)) = some [1, 1] := rfl
example : ((selectRepeat 2 nested).map (fun selected => selected.repeatSite.next.nodeCount)) = some 1 := rfl

def boundBody : Region protocolDialect original.context original.outputs :=
  .bind original.region (.ret (.cons .here (.cons (.there .here) .nil)))
example : (repeatInventory boundBody).map (·.position) = [[0]] := rfl

/-- Both request frontends share this decoder; paths come from its witness. -/
example : ((ZkcTools.StructuredSource.NormalForms.selectBody boundBody (.str "same")).map (·.path)) =
    .ok [0, 0] := by kernel_rfl
example : ((ZkcTools.StructuredSource.NormalForms.selectBody nested (.str "same")).map (fun _ => ())) =
    .error "normal-form-repeat-ambiguous" := by kernel_rfl
example : ((ZkcTools.StructuredSource.NormalForms.selectBody nested (.str "missing")).map (fun _ => ())) =
    .error "normal-form-repeat" := by kernel_rfl
example : ((ZkcTools.StructuredSource.NormalForms.selectBody nested .null).map (·.path)) = .ok [] := rfl
example : ((ZkcTools.StructuredSource.NormalForms.selectBody nested (.bool false)).map (fun _ => ())) =
    .error "normal-form-repeat" := rfl
example : ((ZkcTools.StructuredSource.NormalForms.selectBody nested (.arr #[])).map (fun _ => ())) =
    .error "normal-form-repeat" := rfl

example : (checkedRepeat 1 nested (by kernel_rfl)).repeatSite = original := rfl
example : (checkedRepeat 1 nested (by kernel_rfl)).occurrence.position = [0] := rfl

private theorem refuseBy {α : Type} {sourceInputs sourceOutputs : List Ty}
    {source : Region protocolDialect sourceInputs sourceOutputs} {site : RepeatSite}
    (observe : RepeatSite → α) (absent : observe site ∉ (repeatSites source).map observe) :
    ¬ Nonempty (RepeatAt site source) := by
  intro occurrence
  exact absent (List.mem_map.mpr ⟨site, (mem_repeatSites_iff site).mpr occurrence, rfl⟩)

def changedCount : RepeatSite :=
  { original with operands := .cons (.there .here) (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil))) }

def swappedState : RepeatSite :=
  { original with operands := .cons .here (.cons (.there (.there .here)) (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))) }

def changedCapture : RepeatSite :=
  { original with operands := (.cons .here
      (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there .here) .nil)))) }

def changedScope : RepeatSite := { original with spec := { spec with stateScopes := [[1], [0, 1]] } }
def changedMaximum : RepeatSite := { original with spec := { spec with maximum := 5 } }
def changedRoles : RepeatSite := { original with spec := { spec with roles := [1, 0] } }
def changedBody : RepeatSite :=
  { original with body := .ret (.cons (.there .here) (.cons (.there (.there .here)) .nil)) }
def changedContinuation : RepeatSite := { original with next := .stop .reject }
def changedContext : RepeatSite :=
  ⟨[.index, .index, .index, .index, .index], original.outputs, spec, "same",
    .cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil))), callback,
    .ret (.cons .here (.cons (.there .here) .nil))⟩

private def returnIndices {inputs outputs : List Ty} : Region protocolDialect inputs outputs → List Nat
  | .ret values => values.indices
  | _ => []

example : ¬ Nonempty (RepeatAt changedCount original.region) := by
  apply refuseBy (fun site => site.operands.indices); decide
example : ¬ Nonempty (RepeatAt swappedState original.region) := by
  apply refuseBy (fun site => site.operands.indices); decide
example : ¬ Nonempty (RepeatAt changedCapture original.region) := by
  apply refuseBy (fun site => site.operands.indices); decide
example : ¬ Nonempty (RepeatAt changedScope original.region) := by
  apply refuseBy (fun site => site.spec.stateScopes); decide
example : ¬ Nonempty (RepeatAt changedMaximum original.region) := by
  apply refuseBy (fun site => site.spec.maximum); decide
example : ¬ Nonempty (RepeatAt changedRoles original.region) := by
  apply refuseBy (fun site => site.spec.roles); decide
example : ¬ Nonempty (RepeatAt changedBody original.region) := by
  apply refuseBy (fun site => returnIndices site.body); decide
example : ¬ Nonempty (RepeatAt changedContinuation original.region) := by
  apply refuseBy (fun site => returnIndices site.next); decide
example : ¬ Nonempty (RepeatAt changedContext original.region) := by
  apply refuseBy (fun site => site.context); decide

/-- A failed exact association cannot be used to recover occurrence evidence. -/
example : (selectRepeat 0 original.region).map (·.repeatSite) ≠ some changedCount := by
  intro same
  have occurrence := selectedRepeat same
  exact (refuseBy (fun site => site.operands.indices) (by decide)) ⟨occurrence⟩

example {interface : PIR.Signature} (meaning : RegionMeaning protocolDialect interface)
    (env : Environment meaning.Value (.index :: (spec.state ++ spec.captures))) :
    callback.denote meaning env = .done (.cons (env (.there .here))
      (.cons (env (.there (.there (.there .here)))) .nil)) := rfl

example {interface : PIR.Signature} (meaning : RegionMeaning protocolDialect interface)
    (env : Environment meaning.Value (.index :: (spec.state ++ spec.captures))) :
    (Region.stop .reject : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state).denote
      meaning env = .halt .reject := rfl

/-- Nested and sequential callbacks for complete generator admission checks. -/
def rootWithLabels (outer inner suffix : String) : Function := { Tests.StructuredBindingsGeneric.root with
  inputs := [.index, .index, .index, .index]
  outputs := [.index, .index]
  interface := some ⟨["Alice", "Bob"], List.replicate 4 ["Alice", "Bob"], [["Alice"], ["Alice", "Bob"]]⟩
  body := .block [
    .instruction (.protocolRepeat 2 3 ["Alice", "Bob"] [["Alice"], ["Alice", "Bob"]])
      [0, 1, 2, 3] [.index, .index]
      [.region [.index, .index, .index, .index] [.index, .index] (.block [
        .instruction (.protocolRepeat 2 3 ["Alice", "Bob"] [["Alice"], ["Alice", "Bob"]])
          [0, 1, 2, 3] [.index, .index]
          [.region [.index, .index, .index, .index] [.index, .index] (.block [] (.yield [1, 3]))] inner
      ] (.yield [0, 1]))] outer,
    .instruction (.protocolRepeat 2 3 ["Alice", "Bob"] [["Alice"], ["Alice", "Bob"]])
      [2, 0, 1, 5] [.index, .index]
      [.region [.index, .index, .index, .index] [.index, .index] (.block [
        .instruction (.booleanConstant false) [] [.boolean] [] "",
        .instruction (.guard "Alice") [0] [] [] "reject"
      ] (.yield [2, 4]))] suffix
  ] (.ret [0, 1]) }

def root : Function := rootWithLabels "outer" "inner" "suffix"
def snapshot : Snapshot := { Tests.StructuredBindingsGeneric.snapshot with definitions := [.function root] }

/-- The inventory handles equal labels on the typed carrier without relaxing
the independent snapshot admission rule. -/
example : (check { snapshot with definitions := [.function (rootWithLabels "same" "same" "same")] }).map
    (fun _ => ()) = .error "structured-duplicate-site" := by decide +kernel

def program : Program := (check snapshot).toOption.get (by decide +kernel)

/-- Identical callback functions at distinct lexical contexts and operands.
Function spelling must not merge their occurrence certificates. -/
def equalBodiesRoot : Function := { root with
  body := .block [
    .instruction (.protocolRepeat 2 3 ["Alice", "Bob"] [["Alice"], ["Alice", "Bob"]])
      [0, 1, 2, 3] [.index, .index]
      [.region [.index, .index, .index, .index] [.index, .index] (.block [] (.yield [1, 3]))] "first",
    .instruction (.protocolRepeat 2 3 ["Alice", "Bob"] [["Alice"], ["Alice", "Bob"]])
      [2, 1, 3, 5] [.index, .index]
      [.region [.index, .index, .index, .index] [.index, .index] (.block [] (.yield [1, 3]))] "second"
  ] (.ret [0, 1]) }
def equalBodiesSnapshot : Snapshot := { snapshot with definitions := [.function equalBodiesRoot] }
def equalBodiesProgram : Program := (check equalBodiesSnapshot).toOption.get (by decide +kernel)

example : (repeatInventory (program.payload.protocols.get ⟨0, by decide +kernel⟩).body).length = 3 :=
  by kernel_rfl
example : (repeatSites (program.payload.protocols.get ⟨0, by decide +kernel⟩).body).map (·.spec.captures) =
    [[.index], [.index], [.index]] := by kernel_rfl

end Tests.RepeatOccurrences

/-- Generate only this small fixture. Kernel checks run on the emitted modules
in a scratch directory; no repository roots or manifests are regenerated. -/
def Tests.RepeatOccurrences.checkGenerated (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected scratch output directory")
  let directory := System.FilePath.mk directory
  IO.FS.createDirAll directory
  let directory ← IO.FS.realPath directory
  let unwrap : Except String String → IO String
    | .ok text => pure text
    | .error reason => throw (IO.userError reason)
  let leanPath := directory.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""
  let compile := fun (name : String) => IO.Process.output {
    cmd := "lean"
    args := #["-j2", "-R", directory.toString, "-DwarningAsError=true", "-DautoImplicit=false",
      "-o", (directory / (name ++ ".olean")).toString, (directory / (name ++ ".lean")).toString]
    env := #[("LEAN_PATH", some leanPath)] }
  for (stem, program, programName, snapshotName) in [
      ("Repeat", Tests.RepeatOccurrences.program, "program", "snapshot"),
      ("EqualBodies", Tests.RepeatOccurrences.equalBodiesProgram, "equalBodiesProgram", "equalBodiesSnapshot")] do
    let output : ZkcTools.StructuredSource.Bindings.Output := {
      moduleName := stem ++ "Bindings"
      sourceModule := "Tests.RepeatOccurrences"
      programExpression := "Tests.RepeatOccurrences." ++ programName
      importedExpression := "(⟨Tests.RepeatOccurrences." ++ programName ++
        ", by kernel_rfl⟩ : Imported Tests.RepeatOccurrences." ++ snapshotName ++ ")" }
    let callbacks ← unwrap (ZkcTools.StructuredSource.Bindings.callbacksSource program output)
    -- One projected complete site per lexical callback, shared across roles.
    let count := program.payload.protocols.foldl (fun count definition =>
      count + (Zkc.Source.Structured.Bindings.repeatInventory definition.body).length) 0
    unless (callbacks.splitOn "checkedRepeat ").length == count + 1 do
      throw (IO.userError "repeat selection was duplicated per role")
    let sources := [
      (output.moduleName, ← unwrap (ZkcTools.StructuredSource.Bindings.source program output)),
      (output.moduleName ++ "Callbacks", callbacks)]
    -- The nested fixture checks complete optional frames. Its hidden nested
    -- state is not a statically absent normal-form component. Scope-projected
    -- role views are checked on the equal-body fixture; the maintained nested
    -- role-view control separately covers nested public state.
    let sources ← if stem == "EqualBodies" then do
      pure (sources ++ [(stem ++ "Views", ← unwrap (ZkcTools.StructuredSource.Bindings.RoleViews.source program
        {output with moduleName := stem ++ "Views", sourceModule := output.moduleName ++ "Callbacks"}
        output.moduleName (ZkcTools.StructuredSource.Bindings.RoleViews.ordinalNames program)))])
      else pure sources
    for (name, source) in sources do
      IO.FS.writeFile (directory / (name ++ ".lean")) source
      let result ← compile name
      IO.FS.writeFile (directory / (name ++ ".log")) (result.stdout ++ result.stderr)
      unless result.exitCode == 0 do
        throw (IO.userError ("generated repeat fixture failed: " ++ name ++ "\n" ++ result.stdout ++ result.stderr))
  let contextChecks := "import EqualBodiesViews\nopen Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings\nopen EqualBodiesBindingsCallbacks\nexample : protocol0Callback0Body = protocol0Callback1Body := by kernel_rfl\nexample : protocol0Callback0Site.context ≠ protocol0Callback1Site.context := by decide +kernel\nexample : protocol0Callback0Site.operands.indices ≠ protocol0Callback1Site.operands.indices := by decide +kernel\nexample : protocol0Callback0Occurrence.position ≠ protocol0Callback1Occurrence.position := by decide +kernel\n"
  IO.FS.writeFile (directory / "ContextChecks.lean") contextChecks
  let result ← compile "ContextChecks"
  unless result.exitCode == 0 do throw (IO.userError (result.stdout ++ result.stderr))
  for (name, claim) in [
      ("WrongOccurrence", "example : (selectRepeat 0 EqualBodiesBindings.definition0.body).map (·.repeatSite) = some protocol0Callback1Site := by kernel_rfl\n"),
      ("WrongPosition", "example : protocol0Callback0Occurrence.position = protocol0Callback1Occurrence.position := by kernel_rfl\n")] do
    IO.FS.writeFile (directory / (name ++ ".lean")) ("import EqualBodiesViews\nopen Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings\nopen EqualBodiesBindingsCallbacks\n" ++ claim)
    let result ← compile name
    IO.FS.writeFile (directory / (name ++ ".log")) (result.stdout ++ result.stderr)
    unless result.exitCode != 0 && (result.stdout.splitOn "(kernel)").length > 1 do
      throw (IO.userError ("wrong association did not fail in kernel: " ++ name ++ "\n" ++ result.stdout ++ result.stderr))
  IO.println "RepeatOccurrences: complete callback/role equations, shared selections and exact occurrence refusals checked"

end
