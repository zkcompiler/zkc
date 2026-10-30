module

public import ZkcSecurityExamples.Generation.Roots.Catalogue
public meta import ZkcSecurityExamples.Generation.Roots.Catalogue
public meta import ZkcSecurityExamples.Generation.Roots.SubjectImports
public import ZkcSecurityTools.Generation.SubjectABI
public meta import ZkcSecurityTools.Generation.SubjectABI
public import ZkcSecurityTools.Generation.OriginalEndpoint
public meta import ZkcSecurityTools.Generation.OriginalEndpoint
public import ZkcSecurityTools.Generation.RootCompleteness
public meta import ZkcSecurityTools.Generation.RootCompleteness

public import ZkcSecurityExamples.Generation.TargetSourceAliasesCatalogue
public meta import ZkcSecurityExamples.Generation.TargetSourceAliasesCatalogue

@[expose] public section

/-! Production endpoints consume installed original-source laws. The catalogue
owns proof selection; admitted ABIs and artifacts supply structural metadata.
The complete connection is generated separately by the shared source-to-participant
certificate builder. No scalar or family-specific connection is emitted here. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace ZkcSecurity.Generation.Roots
open ZkcTools.StructuredSource.Root
open ZkcSecurity.Generation

def soundnessOutput (root : Selection) : OriginalEndpoint.Output where
  moduleName := root.componentModule "Soundness"
  namespaceName := root.componentNamespace "Soundness"
  subjectModule := root.subjectModule
  subjectNamespace := root.subjectNamespace
  methodModule := root.securityModule ++ ".Soundness"
  sampling := root.mathematics.modelNamespace ++ "." ++ root.mathematics.sampling
  capabilities := root.mathematics.modelNamespace ++ "." ++ root.mathematics.capabilities
  schedule := root.securityNamespace ++ ".Soundness.schedule"
  validatorCost := root.securityNamespace ++ ".Soundness.validatorCost"
  chargedExport := root.securityNamespace ++ ".Soundness.reductionExport"
  scalar := some ⟨root.securityNamespace ++ ".Soundness.scalarBound", root.securityNamespace ++ ".Soundness.scalar_bound"⟩

def completenessSelection (root : Selection) : RootCompleteness.Selection where
  moduleName := root.componentModule "Completeness"
  namespaceName := root.componentNamespace "Completeness"
  subjectModule := root.subjectModule
  subjectNamespace := root.subjectNamespace
  error := .zero

def completenessClaimsOutput (root : Selection) : FixedCompletenessOutput :=
  RootCompleteness.claimsOutput (completenessSelection root) {
    capabilities := root.mathematics.modelNamespace ++ "." ++ root.mathematics.capabilities }

def claimLibraryOutput (root : Selection) : DomainClaimLibraryOutput :=
  let proofs := root.componentNamespace "Soundness"
  { moduleName := root.subjectModule ++ "SoundnessRegistration"
    namespaceName := root.subjectNamespace ++ "SoundnessRegistration"
    imports := [root.subjectModule, root.componentModule "Soundness"]
    subjectExpression := root.subjectNamespace ++ ".validatorSubject"
    artifactsExpression := root.subjectNamespace ++ ".validatorArtifacts"
    capabilitiesExpression := proofs ++ ".capabilities"
    applicationParameter := some "application"
    theoremMethods := [("fs.keyed_soundness", 0, proofs ++ ".scalar_meaning"),
      ("fs.keyed_charged", 0, proofs ++ ".charged_meaning")]
    theoremNormalization := [proofs ++ ".schedule", proofs ++ ".validatorCost", proofs ++ ".scalarBound"] ++
      ["schedule", "price", "priceBound", "budget", "validatorCost", "scalarBound"].map
        (fun name => root.securityNamespace ++ ".Soundness." ++ name) ++
      ["ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"] }

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let mut sources : List (String × String × String) :=
    TargetSourceAliasesCatalogue.sources.map fun (name, source) => ("bindings", name, source)
  for root in ← evaluateSelections do
    let metadata ← Lean.Elab.Command.liftTermElabM do
      let subject := Lean.mkIdent ((root.subjectNamespace ++ ".subject").toName)
      let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata $subject)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
    let pair := root.artifacts
    sources := sources ++ [
      ("abi", root.componentModule "ABI", ← require <| SubjectABI.source metadata {
        moduleName := root.componentModule "ABI", namespaceName := root.componentNamespace "ABI",
        subjectModule := root.subjectModule, subjectNamespace := root.subjectNamespace }),
      ("soundness", root.componentModule "Soundness", ← require <| OriginalEndpoint.soundnessSource metadata pair.validator (soundnessOutput root)),
      ("completeness", root.componentModule "Completeness", RootCompleteness.directSource
        (completenessSelection root) root.securityModule
        (root.securityNamespace ++ ".compiled_ideal_complete") root.mathematics.sampling
        ["ZkcSecurity.Domains.PrimeField"]),
      ("completeness-claims", root.subjectModule ++ "CompletenessClaims", fixedCompletenessSource (completenessClaimsOutput root)),
      ("claim-libraries", root.subjectModule ++ "SoundnessRegistration", domainClaimLibrarySource (claimLibraryOutput root))]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `stageSources) : List (String × String × String) := $(Lean.quote sources)))

def generateStage (stage : String) (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  unless stageSources.any (fun (selected, _, _) => selected == stage) do
    throw (IO.userError ("unknown production generation stage: " ++ stage))
  writeSources directory (stageSources.filterMap fun (selected, name, source) =>
    if selected == stage then some (name, source) else none)

end ZkcSecurity.Generation.Roots
