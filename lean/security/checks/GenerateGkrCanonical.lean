import ZkcSecurity.Realizations.Gkr.Canonical
import ZkcSecurity.Domains.PrimeField
import ZkcSecurity.Generation.SubjectABI
import ZkcSecurity.Generation.RootCompleteness
import ZkcSecurity.Generation.OriginalEndpoint

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
  let modulePrefix := "ZkcSecurity.Realizations.Gkr.Generated."
  let subject := modulePrefix ++ "Subject"
  let fixed : FixedSubjectOutput := {
    connectionModule := "ZkcExamples.Structured.Generated.Connections.Gkr"
    moduleName := subject
    sourceModule := "ZkcSecurity.Realizations.Gkr.Canonical"
    originalExpression := "ZkcSecurity.Realizations.Gkr.Canonical.original"
    importedExpression := "ZkcSecurity.Realizations.Gkr.Canonical.imported"
    pairModule := "ZkcExamples.Construction.Generated.GkrPair"
    artifactsExpression := "ZkcExamples.Construction.Generated.GkrPair.artifacts"
    modelModule := "ZkcSecurity.Domains.PrimeField"
    modelExpression := "ZkcSecurity.Domains.PrimeField.blsScalarModel"
    targetName := "circuit_outputs"
    originalExportExpression := quoted "sha256:624ace13f9ec65913feab37af7f567746f268585252e9c3bb0708e61e84a70dd"
    producerExportExpression := quoted "sha256:f829be33b7fbf7688a97068f3e195f109cc8021bc40f90719a27510f630d25fc"
    validatorExportExpression := quoted "sha256:fd0bdc7ff8c6e5279e5e0d89df36aa36b3a9180f4ac027c2afb3cd7b9de6bd4b"
    chargeSites := ["output", "left.challenge", "right.challenge", "line_challenge"]
    registryExpression := "(ZkcSecurity.Realizations.Gkr.Relations.registry ZkcSecurity.Domains.PrimeField.blsScalarModel)" }
  let sampling := "ZkcSecurity.Domains.PrimeField.rawSampleable Zkc.Source.Structured.blsModulus"
  let capabilities := "ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)"
  let selection : RootCompleteness.Selection := {
    moduleName := modulePrefix ++ "Completeness", subjectModule := subject, error := .zero }
  let soundness : OriginalEndpoint.Output := {
    moduleName := modulePrefix ++ "Soundness", subjectModule := subject
    methodModule := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness"
    sampling, capabilities
    schedule := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.schedule"
    validatorCost := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.validatorCost"
    chargedExport := "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.reductionExport"
    scalar := some ⟨"ZkcSecurity.Realizations.Gkr.CanonicalSoundness.scalarBound",
      "ZkcSecurity.Realizations.Gkr.CanonicalSoundness.scalar_bound"⟩ }
  let registration : DomainClaimLibraryOutput := {
    moduleName := subject ++ "SoundnessRegistration"
    imports := [subject, soundness.moduleName]
    subjectExpression := subject ++ ".validatorSubject"
    artifactsExpression := subject ++ ".validatorArtifacts"
    capabilitiesExpression := soundness.moduleName ++ ".capabilities"
    applicationParameter := some "application"
    theoremMethods := [("fs.keyed_soundness", 0, soundness.moduleName ++ ".scalar_meaning"),
      ("fs.keyed_charged", 0, soundness.moduleName ++ ".charged_meaning")]
    theoremNormalization := ["schedule", "validatorCost", "scalarBound"].map
      (soundness.moduleName ++ "." ++ ·) ++
      ["schedule", "validatorCost", "scalarBound"].map
        ("ZkcSecurity.Realizations.Gkr.CanonicalSoundness." ++ ·) ++
      ["schedule", "price", "priceBound", "validatorCost", "scalarBound"].map
        ("ZkcSecurity.Realizations.Gkr.CanonicalSchedule." ++ ·) ++
      ["ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"] }
  let sources := [
    (subject, fixedSubjectSource fixed),
    (modulePrefix ++ "ABI", ← require <| SubjectABI.source metadata {
      moduleName := modulePrefix ++ "ABI", subjectModule := subject }),
    (selection.moduleName, RootCompleteness.directSource selection
      "ZkcSecurity.Realizations.Gkr.CanonicalCompleteness"
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
