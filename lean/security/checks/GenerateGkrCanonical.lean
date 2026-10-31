import ZkcSecurityExamples.Gkr.Canonical
import ZkcSecurity.Bindings.Models.PrimeField
import ZkcSecurityTools.Generation.SubjectABI
import ZkcSecurityTools.Generation.RootCompleteness
import ZkcSecurityTools.Generation.OriginalEndpoint

/-! Concrete GKR request selection. All mechanical syntax uses the shared
subject, ABI, completeness and soundness printers. The generated modules are
independently checked; these strings provide no theorem evidence. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace GenerateGkrCanonical
open ZkcTools.StructuredSource.Root
open ZkcSecurity.Generation
open ZkcSecurity.Realizations.Gkr

private meta def require {A : Type} : Except String A → Lean.Elab.Command.CommandElabM A
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let metadata ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm
      (← `(SubjectABI.metadata (Canonical.subject ZkcSecurity.Domains.PrimeField.blsScalarModel))) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
  let artifacts ← Lean.Elab.Command.liftTermElabM do
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (Lean.mkConst ``ZkcExamples.Construction.Generated.GkrPair.artifacts)
    Lean.Meta.evalExpr Zkc.Construction.AuthoredPair.Artifacts
      (Lean.mkConst ``Zkc.Construction.AuthoredPair.Artifacts) reduced
  let modulePrefix := "ZkcSecurityExamples.Gkr.Generated."
  let namespacePrefix := "ZkcSecurity.Realizations.Gkr.Generated."
  let subject := modulePrefix ++ "Subject"
  let subjectNamespace := namespacePrefix ++ "Subject"
  let fixed : FixedSubjectOutput := {
    connectionModule := "ZkcExamples.Structured.Generated.Connections.Gkr"
    moduleName := subject
    namespaceName := subjectNamespace
    sourceModule := "ZkcSecurityExamples.Gkr.Canonical"
    originalExpression := "ZkcSecurity.Realizations.Gkr.Canonical.original"
    importedExpression := "ZkcSecurity.Realizations.Gkr.Canonical.imported"
    pairModule := "ZkcExamples.Construction.Generated.GkrPair"
    artifactsExpression := "ZkcExamples.Construction.Generated.GkrPair.artifacts"
    modelModule := "ZkcSecurity.Bindings.Models.PrimeField"
    modelExpression := "ZkcSecurity.Domains.PrimeField.blsScalarModel"
    targetName := "circuit_outputs"
    originalExportExpression := quoted "sha256:d73cb1755bed132e32367f16a789977f090079fef5c5649a8296cf8e74665133"
    producerExportExpression := quoted "sha256:d68f53c1bfc1a84c277906ac327e7bdee395aedd469f0b776b5b06000112086e"
    validatorExportExpression := quoted "sha256:edab1a2f1991db65a7b9a7560d5614113a4babb83df7307cee4f537f13fb2e7e"
    chargeSites := ["output", "left.challenge", "right.challenge", "line_challenge"]
    registryExpression := "(ZkcSecurity.Realizations.Gkr.Relations.registry ZkcSecurity.Domains.PrimeField.blsScalarModel)" }
  let sampling := "ZkcSecurity.Domains.PrimeField.rawSampleable Zkc.Source.Structured.blsModulus"
  let capabilities := "ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)"
  let selection : RootCompleteness.Selection := {
    moduleName := modulePrefix ++ "Completeness", namespaceName := namespacePrefix ++ "Completeness",
    subjectModule := subject, subjectNamespace, error := .zero }
  let soundness : OriginalEndpoint.Output := {
    moduleName := modulePrefix ++ "Soundness", namespaceName := namespacePrefix ++ "Soundness",
    subjectModule := subject, subjectNamespace
    methodModule := "ZkcSecurityExamples.Gkr.CanonicalSoundness"
    sampling, capabilities
    schedule := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.schedule"
    validatorCost := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.validatorCost"
    chargedExport := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.reductionExport"
    scalar := some ⟨"ZkcSecurity.Realizations.Gkr.CanonicalSoundness.scalarBound",
      "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.scalar_bound"⟩ }
  let registration : DomainClaimLibraryOutput := {
    moduleName := subject ++ "SoundnessRegistration"
    namespaceName := subjectNamespace ++ "SoundnessRegistration"
    imports := [subject, soundness.moduleName]
    subjectExpression := subjectNamespace ++ ".validatorSubject"
    artifactsExpression := subjectNamespace ++ ".validatorArtifacts"
    capabilitiesExpression := soundness.namespaceName ++ ".capabilities"
    applicationParameter := some "application"
    theoremMethods := [("fs.keyed_soundness", 0, soundness.namespaceName ++ ".scalar_meaning"),
      ("fs.keyed_charged", 0, soundness.namespaceName ++ ".charged_meaning")]
    theoremNormalization := ["schedule", "validatorCost", "scalarBound"].map
      (soundness.namespaceName ++ "." ++ ·) ++
      ["schedule", "validatorCost", "scalarBound"].map
        ("ZkcSecurity.Realizations.Gkr.CanonicalSoundness." ++ ·) ++
      ["schedule", "price", "priceBound", "validatorCost", "scalarBound"].map
        ("ZkcSecurity.Realizations.Gkr.CanonicalSchedule." ++ ·) ++
      ["ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"] }
  let sources := [
    (subject, fixedSubjectSource fixed),
    (modulePrefix ++ "ABI", ← require <| SubjectABI.source metadata {
      moduleName := modulePrefix ++ "ABI", namespaceName := namespacePrefix ++ "ABI",
      subjectModule := subject, subjectNamespace }),
    (selection.moduleName, RootCompleteness.directSource selection
      "ZkcSecurityExamples.Gkr.CanonicalCompleteness"
      "ZkcSecurity.Realizations.Gkr.CanonicalCompleteness.compiled_ideal_complete" sampling),
    (subject ++ "CompletenessClaims", RootCompleteness.claimsSource selection { capabilities }),
    (soundness.moduleName, ← require <| OriginalEndpoint.soundnessSource metadata artifacts.validator soundness),
    (registration.moduleName, domainClaimLibrarySource registration)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name}"
end GenerateGkrCanonical

def main := GenerateGkrCanonical.main
