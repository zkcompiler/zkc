import ZkcTools.StructuredSource.Bindings.Inputs
import ZkcTools.StructuredSource.OriginalRoot

/-! Dedicated client of the generic input and nominal template printers.
Selection inspects admitted typed signatures. The generated proofs check the
entire exported body, helper table and immutable capture. -/
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource

def main (args : List String) : IO Unit := do
  let [snapshotPath, directory] := args | throw (IO.userError "expected snapshot and output directory")
  let raw ← IO.FS.readFile snapshotPath
  let snapshot ← match Structured.Format.parse raw >>= Structured.Format.snapshot with
    | .ok snapshot => pure snapshot
    | .error reason => throw (IO.userError reason)
  IO.println "parsed snapshot"
  (← IO.getStdout).flush
  let program ← match Structured.check snapshot with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  IO.println "admitted snapshot"
  (← IO.getStdout).flush
  let [round, root] := program.payload.protocols
    | throw (IO.userError "mixed-sumcheck-protocol-selection")
  unless root.signature == program.payload.entry.signature &&
      round.signature.roles.length == 2 && root.signature.roles.length == 2 &&
      round.inputs == [.field "koala-bear", .field "koala-bear",
        .vector "koala-bear.ext8-binomial3", .field "koala-bear.ext8-binomial3", .service "random.koala-bear.ext8-binomial3/0"] &&
      round.outputs == [.vector "koala-bear.ext8-binomial3", .field "koala-bear.ext8-binomial3"] &&
      root.inputs == [.field "koala-bear", .field "koala-bear", .field "koala-bear",
        .service "random.koala-bear.ext8-binomial3/0"] && root.outputs == [.boolean] do
    throw (IO.userError "mixed-sumcheck-protocol-types")
  let [embedding] := program.payload.definitions.filter (fun definition =>
      definition.kind == .local && definition.inputs == [.field "koala-bear"] &&
      definition.outputs == [.field "koala-bear.ext8-binomial3"])
    | throw (IO.userError "mixed-sumcheck-embedding-selection")
  IO.println "selected embedding"
  (← IO.getStdout).flush
  let signature : Signature := ⟨[⟨embedding.helper, .returns [], []⟩], false, true,
    (program.payload.definitions.filter (·.helper != embedding.helper)).map (·.helper), []⟩
  let modulePrefix := "ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated"
  IO.println "rendering typed inputs"
  (← IO.getStdout).flush
  let mut sources := [(modulePrefix ++ ".Inputs", Bindings.inputsSource program (modulePrefix ++ ".Inputs") (modulePrefix ++ ".Data"))]
  for (definition, index, label) in [(round, 0, "Round"), (root, 1, "Root")] do
    for role in [0, 1] do
      let moduleName := modulePrefix ++ "." ++ label ++ (if role == 0 then "Producer" else "Verifier")
      let output : OriginalRoot.TemplateOutput := {
        moduleName, sourceModule := modulePrefix ++ ".Inputs", programExpression := modulePrefix ++ ".Inputs.program"
        definitionIndex := index, role
        signature := { signature with callees := (program.payload.protocols.take index).map fun callee =>
          ⟨callee.signature, role, Bindings.optionalPattern callee.inputs, []⟩ } }
      IO.println s!"rendering {moduleName}"
      (← IO.getStdout).flush
      match OriginalRoot.templateSource program output with
      | .error reason => throw (IO.userError reason)
      | .ok source => sources := sources ++ [(moduleName, source)]
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name}"
