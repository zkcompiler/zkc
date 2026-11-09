module

public import Zkc.Tools.IR.StructuredSource.Bindings.RoleViews
public import Zkc.Tools.IR.StructuredSource.Bindings.Ledger
public import Zkc.Tools.IR.StructuredSource.Bindings.PresentInputs
public import Zkc.Tools.IR.StructuredSource.Bindings.SourceInstallation
public import Zkc.Tests.IR.StructuredNestedRoleData

@[expose] public section

namespace Tests.Generators.RoleViewControls
open Zkc.Source.Structured ZkcTools.StructuredSource.Bindings

def write (path content : String) : IO Unit := do
  let path := System.FilePath.mk path
  if ← path.pathExists then
    if (← IO.FS.readFile path) == content then return
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path content

def generate (snapshot : Snapshot) (sourceModule sourceExpression snapshotExpression stem : String) : IO Unit := do
  let program ← match check snapshot with
    | .ok program => pure program
    | .error error => throw (IO.userError error)
  let output : Output := {
    moduleName := "Zkc.Tests.IR.Generated." ++ stem ++ "Bindings"
    namespaceName := "Tests.Generated." ++ stem ++ "Bindings"
    sourceModule := sourceModule
    programExpression := sourceExpression
    importedExpression := "(⟨" ++ sourceExpression ++ ", by kernel_rfl⟩ : Imported " ++ snapshotExpression ++ ")" }
  let unwrap {α} : Except String α → IO α
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let bindings ← unwrap (source program output)
  let callbacks ← unwrap (callbacksSource program output)
  let relocated : Output := { output with moduleName := "Relocated." ++ output.moduleName }
  unless bindings == (← unwrap (source program relocated)) do
    throw (IO.userError "binding-module-relocation-changed-declarations")
  let relocateImport := fun (text : String) =>
    text.replace ("public import " ++ output.moduleName) ("public import " ++ relocated.moduleName)
  unless relocateImport callbacks == (← unwrap (callbacksSource program relocated)) &&
      relocateImport (callerSourceHeader output) == callerSourceHeader relocated do
    throw (IO.userError "callback-module-relocation-changed-declarations")
  let ledger := obligationLedger program output
  let relocatedLedger := obligationLedger program relocated
  for field in ["structural", "mathematical_helpers"] do
    unless (← unwrap (ledger.getObjVal? field)).compress ==
        (← unwrap (relocatedLedger.getObjVal? field)).compress do
      throw (IO.userError "binding-module-relocation-changed-obligation-identities")
  unless (← unwrap (relocatedLedger.getObjValAs? String "module")) == relocated.moduleName do
    throw (IO.userError "binding-ledger-module-identity")
  if stem == "CounterRole" then
    unless (← unwrap (PresentInputs.source program output 0)) ==
        (← unwrap (PresentInputs.source program relocated 0)) do
      throw (IO.userError "present-input-module-relocation-changed-declarations")
  write ("Zkc/Tests/IR/Generated/" ++ stem ++ "Bindings.lean") bindings
  write ("Zkc/Tests/IR/Generated/" ++ stem ++ "BindingsCallbacks.lean") callbacks
  let views : Output := { output with
    moduleName := "Zkc.Tests.IR.Generated." ++ stem ++ "Views"
    namespaceName := "Tests.Generated." ++ stem ++ "Views"
    sourceModule := output.moduleName ++ "Callbacks" }
  let names := RoleViews.ordinalNames program
  let roleViews ← unwrap (RoleViews.source program views output.namespaceName names)
  let relocatedViews : Output := { views with
    moduleName := "Relocated." ++ views.moduleName
    sourceModule := relocated.moduleName ++ "Callbacks" }
  unless relocateImport roleViews ==
      (← unwrap (RoleViews.source program relocatedViews output.namespaceName names)) do
    throw (IO.userError "role-view-module-relocation-changed-declarations")
  write ("Zkc/Tests/IR/Generated/" ++ stem ++ "Views.lean") roleViews

def main : IO Unit := do
  generate Tests.StructuredBindingsGeneric.snapshot "Zkc.Tests.IR.StructuredBindingsGeneric"
    "Tests.StructuredBindingsGeneric.program" "Tests.StructuredBindingsGeneric.snapshot" "CounterRole"
  generate Tests.StructuredNestedRoleData.snapshot "Zkc.Tests.IR.StructuredNestedRoleData"
    "Tests.StructuredNestedRoleData.program" "Tests.StructuredNestedRoleData.snapshot" "NestedRole"
end Tests.Generators.RoleViewControls
