module

public import ZkcTools.StructuredSource.Bindings.RoleViews
public import Tests.StructuredBindingsDispatchData

@[expose] public section

namespace Tests.Generators.RoleViewControls
open Zkc.Source.Structured ZkcTools.StructuredSource.Bindings

def nestedRoot : Function := { Tests.StructuredBindingsDispatchData.root with
  body := .block [
    .instruction (.protocolApply "middle" ["Bob", "Alice"]) [0, 1] [.index] [] "first",
    .instruction (.protocolApply "middle" ["Alice", "Bob"]) [0, 2] [.index] [] "second",
    .instruction (.protocolRepeat 1 3 ["Alice", "Bob"] [["Alice", "Bob"]]) [2, 0] [.index]
      [.region [.index, .index] [.index] (.block [
        .instruction (.protocolApply "leaf" ["Bob", "Alice"]) [0, 1] [.index] [] "before",
        .instruction (.protocolRepeat 1 3 ["Alice", "Bob"] [["Alice", "Bob"]]) [1, 0] [.index]
          [.region [.index, .index] [.index] (.block [
            .instruction (.protocolApply "leaf" ["Alice", "Bob"]) [0, 1] [.index] [] "inside",
            .instruction (.protocolApply "leaf" ["Bob", "Alice"]) [1, 0] [.index] [] "again"
          ] (.yield [0]))] "inner"
      ] (.yield [0]))] "outer"
  ] (.ret [0]) }

def nested : Snapshot := { Tests.StructuredBindingsDispatchData.snapshot with
  definitions := [.function nestedRoot, .function Tests.StructuredBindingsDispatchData.leaf,
    .function Tests.StructuredBindingsDispatchData.booleanLeaf,
    .function Tests.StructuredBindingsDispatchData.middle] }

def write (path content : String) : IO Unit := do
  IO.FS.createDirAll (System.FilePath.mk path).parent.get!
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

def nestedProgram : Program := (check nested).toOption.get (by decide +kernel)

def main : IO Unit := do
  generate Tests.StructuredBindingsGeneric.snapshot "Tests.StructuredBindingsGeneric"
    "Tests.StructuredBindingsGeneric.program" "Tests.StructuredBindingsGeneric.snapshot" "CounterRole"
  generate nested "Tests.Generators.RoleViewControls"
    "Tests.Generators.RoleViewControls.nestedProgram" "Tests.Generators.RoleViewControls.nested" "NestedRole"
end Tests.Generators.RoleViewControls
