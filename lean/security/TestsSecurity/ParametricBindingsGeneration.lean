module

public import ZkcSecurity.Generation.OriginalSecurityBindings
meta import ZkcSecurity.Generation.OriginalSecurityBindings
public import TestsSecurity.ParametricBindings
meta import TestsSecurity.ParametricBindings

@[expose] public section

/-! Fresh candidates through the production OriginalRoot and security printers.
The independent runner compiles emitted templates, installations and refusals. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ParametricBindingsGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource ZkcSecurity.Generation

private meta unsafe def evaluate (α : Type) (name : Lean.Name) (expression : Lean.Expr) :
    Lean.Elab.Command.CommandElabM α :=
  Lean.Elab.Command.liftTermElabM do
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce expression
    Lean.Meta.evalExpr α (Lean.mkConst name) reduced

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let mut sources : List (String × String) := []
  for label in ["Mixed", "Gates"] do
    let fixture := "TestsSecurity.ParametricBindings." ++ label
    let snapshot ← evaluate Structured.Snapshot ``Structured.Snapshot
      (Lean.mkApp (Lean.mkConst ``Structured.Program.snapshot) (Lean.mkConst ((fixture ++ ".program").toName)))
    let program ← require (Structured.check snapshot)
    let signature ← evaluate Signature ``Signature (Lean.mkConst ((fixture ++ ".signature").toName))
    let moduleName := "ParametricClients." ++ label
    let selected : OriginalRoot.TemplateOutput := {
      moduleName, sourceModule := "TestsSecurity.ParametricBindings"
      programExpression := fixture ++ ".program", definitionIndex := 0, role := 1, signature }
    sources := sources ++ [(moduleName, ← require (OriginalRoot.templateSource program selected))]
    let output : OriginalSecurityBindings.TemplateInstallation := {
      moduleName := moduleName ++ "Installation", templateModule := moduleName
      mathematicsModule := "TestsSecurity.ParametricBindings"
      model := if label == "Mixed" then "ZkcSecurity.Domains.KoalaBearModel.model" else fixture ++ ".model"
      modelLaws := fixture ++ ".modelLaws"
      domain := if label == "Mixed" then "koala-bear.ext8-binomial3" else "bls12-381.fr"
      fieldLaw := if label == "Mixed" then fixture ++ ".fieldLaw" else "Field.toIsField (ZMod blsModulus)"
      results := if label == "Mixed" then fixture ++ ".results" else "emptyResults model"
      helperLaws := if label == "Mixed" then fixture ++ ".helperLaws input" else "emptyLaws _ input"
      processes := "fun entry => entry.elim0", calleeLaws := "fun entry => entry.elim0"
      role := 1, roster := 2 }
    sources := sources ++ [(output.moduleName, OriginalSecurityBindings.templateBindings output)]
    if label == "Mixed" then
      for (suffix, wrong) in [("WrongModel", { output with model := "ZkcSecurity.Domains.PrimeField.blsScalarModel" }),
          ("WrongHelper", { output with results := fixture ++ ".wrongResults" }),
          ("WrongDomain", { output with domain := "uninstalled-field" })] do
        let wrong := { wrong with moduleName := "ParametricClients." ++ suffix }
        sources := sources ++ [(wrong.moduleName, OriginalSecurityBindings.templateBindings wrong)]
    else
      let signature : Signature := { signature with callees := Bindings.keys program }
      let rootOutput := { selected with moduleName := "ParametricClients.GatesRoot", definitionIndex := 1, signature }
      sources := sources ++ [(rootOutput.moduleName, ← require (OriginalRoot.templateSource program rootOutput))]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name} ({source.utf8ByteSize} bytes)"

end TestsSecurity.ParametricBindingsGeneration
