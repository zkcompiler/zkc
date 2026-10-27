module

public import ZkcTools.StructuredSource.TemplateInstallation
meta import ZkcTools.StructuredSource.TemplateInstallation
public import TestsSecurity.ParametricBindings
meta import TestsSecurity.ParametricBindings

@[expose] public section

/-! Fresh candidates through the generic OriginalRoot template and library-law printer.
The independent runner compiles emitted templates, installations and refusals. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ParametricBindingsGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource

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
    let templateSource ← require (OriginalRoot.templateSource program selected)
    sources := sources ++ [(moduleName, templateSource)]
    if label == "Mixed" then
      sources := sources ++ [("ParametricClients.WrongRole",
        (templateSource.replace moduleName "ParametricClients.WrongRole").replace
          "def role : Nat := 1" "def role : Nat := 0")]
    let output : TemplateInstallation.Output := {
      moduleName := moduleName ++ "Installation", templateModule := moduleName
      mathematicsModule := "TestsSecurity.ParametricBindings"
      model := if label == "Mixed" then "ZkcSecurity.Domains.KoalaBearModel.model" else fixture ++ ".model"
      modelLaws := fixture ++ ".modelLaws"
      applicability := [
        { name := "domainApplicable", proposition := "program.snapshot.catalogue.require " ++
            (if label == "Mixed" then "\"koala-bear.ext8-binomial3\"" else "\"bls12-381.fr\"") ++ " .field \"Field\" = .ok ()",
          proof := "by decide +kernel" },
        { name := "fieldLaw", proposition := "IsField (model.Field " ++
            (if label == "Mixed" then "\"koala-bear.ext8-binomial3\"" else "\"bls12-381.fr\"") ++ ")",
          proof := if label == "Mixed" then fixture ++ ".fieldLaw" else "Field.toIsField (ZMod blsModulus)" }]
      results := if label == "Mixed" then fixture ++ ".results" else "emptyResults model"
      helperLaws := if label == "Mixed" then fixture ++ ".helperLaws input" else "emptyLaws _ input"
      processes := "fun entry => entry.elim0", calleeLaws := "fun entry => entry.elim0"
      }
    sources := sources ++ [(output.moduleName, TemplateInstallation.source output)]
    if label == "Mixed" then
      let wrongDomain : TemplateInstallation.Output := { output with
        applicability := [{ name := "domainApplicable"
                            proposition := "program.snapshot.catalogue.require \"uninstalled-field\" .field \"Field\" = .ok ()"
                            proof := "by decide +kernel" }] }
      for (suffix, wrong) in [("WrongModel", { output with model := "ZkcSecurity.Domains.PrimeField.blsScalarModel" }),
          ("WrongHelper", { output with results := fixture ++ ".wrongResults" }),
          ("WrongDomain", wrongDomain)] do
        let wrong := { wrong with moduleName := "ParametricClients." ++ suffix }
        sources := sources ++ [(wrong.moduleName, TemplateInstallation.source wrong)]
    else
      let signature : Signature := { signature with callees := Bindings.keys program }
      let rootOutput := { selected with moduleName := "ParametricClients.GatesRoot", definitionIndex := 2, signature }
      let rootSource ← require (OriginalRoot.templateSource program rootOutput)
      sources := sources ++ [(rootOutput.moduleName, rootSource)]
      sources := sources ++ [("ParametricClients.WrongCapture",
        ((rootSource.replace rootOutput.moduleName "ParametricClients.WrongCapture").replace
          "def capture (model : DomainModel) : ProtocolTable model.Value (Interface model) :=\n  (program.payload.protocols.take 2)"
          "def capture (model : DomainModel) : ProtocolTable model.Value (Interface model) :=\n  (program.payload.protocols.take 0)"))]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name} ({source.utf8ByteSize} bytes)"

end TestsSecurity.ParametricBindingsGeneration
