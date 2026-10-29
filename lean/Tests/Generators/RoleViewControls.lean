module

public import ZkcTools.StructuredSource.Bindings.RoleViews
public import Tests.StructuredNestedRoleData

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
    moduleName := "Tests.Generated." ++ stem ++ "Bindings"
    sourceModule := sourceModule
    programExpression := sourceExpression
    importedExpression := "(⟨" ++ sourceExpression ++ ", by kernel_rfl⟩ : Imported " ++ snapshotExpression ++ ")" }
  let unwrap {α} : Except String α → IO α
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  write ("Tests/Generated/" ++ stem ++ "Bindings.lean") (← unwrap (source program output))
  write ("Tests/Generated/" ++ stem ++ "BindingsCallbacks.lean") (← unwrap (callbacksSource program output))
  let views : Output := { output with
    moduleName := "Tests.Generated." ++ stem ++ "Views"
    sourceModule := output.moduleName ++ "Callbacks" }
  write ("Tests/Generated/" ++ stem ++ "Views.lean")
    (← unwrap (RoleViews.source program views output.moduleName (RoleViews.ordinalNames program)))

def main : IO Unit := do
  generate Tests.StructuredBindingsGeneric.snapshot "Tests.StructuredBindingsGeneric"
    "Tests.StructuredBindingsGeneric.program" "Tests.StructuredBindingsGeneric.snapshot" "CounterRole"
  generate Tests.StructuredNestedRoleData.snapshot "Tests.StructuredNestedRoleData"
    "Tests.StructuredNestedRoleData.program" "Tests.StructuredNestedRoleData.snapshot" "NestedRole"
end Tests.Generators.RoleViewControls
