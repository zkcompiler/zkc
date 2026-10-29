import ZkcTools.StructuredSource.Bindings.RoleViews
import ZkcExamples.Structured.GkrSourceData

/-! GKR presentation spelling only. Visibility, carried positions, callee
operands, masks, signatures and complete bodies are derived from the source.
This catalogue is authored glue and is counted as such. -/
namespace Tests.Generators.GkrPresentations
open Zkc.Source.Structured ZkcTools.StructuredSource.Bindings
open RoleViews

def names : List ProtocolNames := [
  { space := "Rounds", body := "rounds", roles := ["proverRounds", "verifierRounds"],
    inputs := ["add", "mul", "left", "right", "initialPoint", "claim", "rounds", "service"],
    callbacks := [{ body := "round", roles := ["prover", "verifier"], inputs := ["index", "add", "mul", "left", "right", "point", "point", "claim", "service"] }] },
  { space := "Input", body := "input", roles := ["verifier"],
    inputs := ["values", "point", "claim"], callbacks := [] },
  { space := "Root", body := "gkr", roles := ["prover", "verifier"],
    inputs := ["inputs", "outputs", "add", "mul", "layers", "selector", "width", "service"],
    callbacks := [
      { body := "output", roles := ["proverOutput", "verifierOutput"], inputs := ["index", "point", "point", "service"] },
      { body := "layer", roles := ["proverLayer", "verifierLayer"], inputs := ["index", "point", "point", "claim", "inputs", "add", "mul", "layers", "selector", "width", "service"] },
      { body := "coefficient", roles := ["proverCoefficient", "verifierCoefficient"], inputs := ["index", "coefficients", "line"] }] }]

def output : Output := {
  moduleName := "ZkcExamples.Structured.Generated.Presentations.Gkr"
  sourceModule := "ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks"
  programExpression := "ZkcExamples.Structured.GkrSourceViews.program"
  importedExpression := "ZkcExamples.Structured.GkrSourceViews.imported" }

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected output file")
  let program ← match check ZkcExamples.Structured.GkrSourceData.snapshot with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let text ← match source program output "ZkcExamples.Structured.Generated.Bindings.GkrRounds" names with
    | .ok text => pure text
    | .error reason => throw (IO.userError reason)
  IO.FS.createDirAll (System.FilePath.mk path).parent.get!
  IO.FS.writeFile path text
  IO.println "generated GKR scope-derived presentations"
end Tests.Generators.GkrPresentations
