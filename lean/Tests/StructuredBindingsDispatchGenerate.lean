import Tests.StructuredBindingsDispatchData
import ZkcTools.StructuredSource.Bindings.Generate
import ZkcTools.StructuredSource.Bindings.Inputs

/-! Emit focused clients of the actual binding printer. The caller kernel-checks
the emitted modules, including sparse selections and dependent-table lookups. -/
namespace Tests.StructuredBindingsDispatchGenerate
open Zkc.Source.Structured ZkcTools.StructuredSource.Bindings

private def require (result : Except String String) : IO String :=
  match result with
  | .ok text => pure text
  | .error reason => throw (IO.userError reason)

private def occurrenceCount (text fragment : String) : Nat := (text.splitOn fragment).length - 1

private def snapshotFor (count : Nat) : Snapshot :=
  { Tests.StructuredBindingsGeneric.snapshot with
    entry := "counter0"
    definitions := (List.range count).map fun index => .function
      { Tests.StructuredBindingsGeneric.root with name := "counter" ++ toString index }
    contracts := (List.range count).map fun index => ⟨"counter" ++ toString index, []⟩ }

private def output (name : String) : Output where
  moduleName := name
  sourceModule := "DispatchInputs"
  programExpression := "DispatchInputs.program"
  importedExpression := "DispatchInputs.imported"

/-- Compare the lookup at one typed key, including optional environments and
the complete masked return. These are identities of open processes. -/
private def lookupControl (entry protocol role : Nat) (selected : Bool) : String :=
  let key := "⟨" ++ toString entry ++ ", by decide +kernel⟩"
  let call := "protocol3Role1Callees " ++ key ++ " ctx binders"
  let expected := if selected then
      roleName protocol role ++ "View ctx ((Zkc.Source.Structured.Bindings.optionalPattern " ++
        "definition" ++ toString protocol ++ ".inputs).environment (ringModel F G) binders)"
    else "Zkc.Source.Structured.Bindings.actualCallees payload calleeKeys " ++ key ++ " ctx binders"
  "example (ctx : ProtocolContext) (binders : NormalForm.Binders (ringModel F G) " ++
    "(NormalForm.calleeAt calleeKeys " ++ key ++ ").pattern.scope) :\n  " ++ call ++
    " = " ++ expected ++ " := by rfl\n"

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let directory := System.FilePath.mk directory
  IO.FS.createDirAll directory
  let program := Tests.StructuredBindingsDispatchData.program
  IO.FS.writeFile (directory / "DispatchInputs.lean") (inputsSource program "DispatchInputs"
    "Tests.StructuredBindingsDispatchData")
  for (name, protocols, roles) in
      [("DispatchAll", [], []), ("DispatchProtocols", [0, 2, 3], []),
       ("DispatchRoles", [], [1]), ("DispatchSparse", [0, 2, 3], [1]),
       ("DispatchRootOnly", [3], [1]), ("DispatchEmpty", [99], [])] do
    let selected : Output := { output name with protocols := protocols, roles := roles }
    let mut text ← require (source program selected)
    if name != "DispatchEmpty" then
      text := text ++ "\nnamespace " ++ name ++ "\nopen Zkc.Source Zkc.Source.Structured\n" ++
        "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n"
      for (entry, protocol, role) in [(0, 0, 0), (1, 0, 1), (2, 1, 0), (3, 1, 1), (5, 2, 1)] do
        let bound := (protocols.isEmpty || protocols.contains protocol) && (roles.isEmpty || roles.contains role)
        text := text ++ lookupControl entry protocol role bound
      -- Even the second selected role must not use views from its own declaration.
      text := text ++ lookupControl 6 3 0 false ++ lookupControl 7 3 1 false
      if (protocols.isEmpty || protocols.contains 1) && (roles.isEmpty || roles.contains 0) then
        text := text ++ "example (value : Bool) : protocol1Role0View (F := F) (G := G) {} " ++
          "(.cons (some value) .nil) = .done (.cons none .nil) := by rfl\n" ++
          "example (value : Bool) : protocol1Role0View (F := F) (G := G) {} " ++
          "(.cons (some value) .nil) ≠ .done (.cons (some value) .nil) := by\n" ++
          "  intro same\n  cases same\n"
      text := text ++ "#print axioms protocol3Role1_certificate\nend " ++ name ++ "\n"
    IO.FS.writeFile (directory / (name ++ ".lean")) text
    IO.println s!"emitted {name}"
  -- Use the same admitted independent protocols as the retained review probe.
  -- There are no helper projection cases in this workload: every update must
  -- occur once, while the shared base proof visits each global key once.
  for count in [1, 2, 4, 8] do
    let admitted ← match check (snapshotFor count) with
      | .ok program => pure program
      | .error reason => throw (IO.userError reason)
    let growthOutput : Output := {
      moduleName := "Probe.Generated", sourceModule := "Probe.Inputs"
      programExpression := "Probe.Inputs.program", importedExpression := "Probe.Inputs.imported" }
    let text ← require (source admitted growthOutput)
    let keyCount := (keys admitted).length
    let dispatch := occurrenceCount text "Fin.cases"
    let updates := occurrenceCount text "Function.update"
    let keyLiterals := occurrenceCount text " : CalleeKey)"
    unless dispatch == 0 && updates == keyCount && keyLiterals == keyCount do
      throw (IO.userError s!"dispatch-growth: {count}: {dispatch} cases, {updates} updates, {keyLiterals} literals, {keyCount} keys")
    IO.FS.writeFile (directory / ("growth-" ++ toString count ++ ".lean.txt")) text
    IO.println s!"protocols={count} keys={keyCount} Fin.cases_nodes={dispatch} updates={updates} key_literals={keyLiterals} characters={text.length}"

end Tests.StructuredBindingsDispatchGenerate
