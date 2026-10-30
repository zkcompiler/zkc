import ZkcSecurityTools.Generation.SigmaCompleteness
import TestsSecurity.RootAssemblyFixture
import TestsSecurity.ABIInstallations.Ordered

/-! Generate fresh checked consumers without depending on moving native root
exports. The separate driver compiles each emitted module and the refusals. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.RootAssemblyGeneration
open ZkcSecurity.Generation

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let metadata ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm
      (← `(SubjectABI.metadata TestsSecurity.RootAssemblyFixture.subject)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
  let pair ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Meta.withTransparency .all <|
      Lean.Meta.reduce (Lean.mkConst ``TestsSecurity.RootAssemblyFixture.artifacts)
    Lean.Meta.evalExpr Zkc.Construction.AuthoredPair.Artifacts
      (Lean.mkConst ``Zkc.Construction.AuthoredPair.Artifacts) expression
  let subjectModule := "TestsSecurity.RootAssemblyFixture"
  let modulePrefix := "CommonAssemblyClients."
  let sampling := "ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus"
  let output : UniformRoot.Output := {
    moduleName := modulePrefix ++ "Readback", subjectModule
    producerModule := modulePrefix ++ "Producer", validatorModule := modulePrefix ++ "Validator"
    abiModule := modulePrefix ++ "ABI", fieldType := "ZMod blsModulus", groupType := "ZMod blsModulus"
    sampling }
  let selection : RootCompleteness.Selection := {
    moduleName := modulePrefix ++ "Direct", subjectModule
    error := ⟨"1", ".natural 1"⟩ }
  let request : RootCompleteness.Request := {
    capabilities := "ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)" }
  let law := modulePrefix ++ "QuantitativeLaw"
  let mut sources := [(modulePrefix ++ "ABI", ← require <| SubjectABI.source metadata {
    moduleName := modulePrefix ++ "ABI", subjectModule })]
  for (role, artifact) in [("Producer", pair.producer), ("Validator", pair.validator)] do
    sources := sources ++ [(modulePrefix ++ role, ← require <| ZkcTools.StructuredSource.Constructed.source artifact {
      moduleName := modulePrefix ++ role, artifactModule := subjectModule
      artifactExpression := subjectModule ++ ".artifacts." ++ role.toLower })]
  sources := sources ++ [(modulePrefix ++ "Readback", ← require <| SigmaCompleteness.source { metadata, output }),
    (law, "module\npublic import " ++ modulePrefix ++ "Readback\n@[expose] public section\n" ++
      "noncomputable section\nnamespace " ++ law ++ "\n" ++
      "open Zkc.Source.Structured Zkc.Construction\n" ++
      "local instance : ∀ event : Domain.Event TestsSecurity.RootAssemblyFixture.subject.domainModel.toCarriers,\n" ++
      "    SampleableType (Domain.Raw event) := " ++ sampling ++ "\n" ++
      "theorem quantitative : ZkcSecurity.Claims.HonestPair.CanonicalCompleteness\n" ++
      "    TestsSecurity.RootAssemblyFixture.subject 1 := TestsSecurity.RootAssemblyFixture.one_of_perfect " ++
      modulePrefix ++ "Readback.compiled_ideal_complete\nend " ++ law ++ "\n"),
    (selection.moduleName, RootCompleteness.directSource selection law (law ++ ".quantitative") sampling),
    (modulePrefix ++ "WrongBound", RootCompleteness.directSource
      { selection with moduleName := modulePrefix ++ "WrongBound", namespaceName := modulePrefix ++ "WrongBound", error := .zero }
      law (law ++ ".quantitative") sampling),
    (modulePrefix ++ "WrongSubject", RootCompleteness.directSource
      { selection with moduleName := modulePrefix ++ "WrongSubject", namespaceName := modulePrefix ++ "WrongSubject", subjectModule := "TestsSecurity.ABIInstallations.Ordered", subjectNamespace := "TestsSecurity.ABIInstallations.Ordered" }
      law (law ++ ".quantitative") "ZkcSecurity.Domains.PrimeField.rawSampleable 5")]
  let receipt := RootCompleteness.claimsOutput selection request
  sources := sources ++ [(receipt.moduleName, RootCompleteness.claimsSource selection request)]
  let wrongReceipt := { receipt with moduleName := modulePrefix ++ "WrongQuantity", namespaceName := modulePrefix ++ "WrongQuantity", errorExpression := ".natural 0" }
  let checkedWrongReceipt := (ZkcTools.StructuredSource.Root.fixedCompletenessSource wrongReceipt).replace
    ("#print axioms completeReceipt")
    ("run_cmd do\n  let env ← Lean.getEnv\n" ++
     "  unless env.contains `CommonAssemblyClients.WrongQuantity.completeEvaluated do\n" ++
     "    throwError \"request failed before canonical evaluation\"\n" ++
     "  if env.contains `CommonAssemblyClients.WrongQuantity.completeReceipt then\n" ++
     "    throwError \"mismatched quantitative theorem produced a receipt\"\n")
  sources := sources ++ [(wrongReceipt.moduleName, checkedWrongReceipt)]
  unless (RootCompleteness.theoremSource selection "proof").contains ".subject (1)" do
    Lean.throwError "quantitative consumer lost its explicit bound"
  unless receipt.proofName == selection.moduleName ++ ".compiled_ideal_complete" &&
      receipt.errorExpression == selection.error.expression do
    Lean.throwError "endpoint/request association diverged"
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `generatedSources) :
    List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, source) in generatedSources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
  IO.FS.writeFile (System.FilePath.mk directory / "sources.json")
    ((Lean.toJson (generatedSources.map (·.1))).compress ++ "\n")

end TestsSecurity.RootAssemblyGeneration
