module

public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.SubjectImports
public import ZkcSecurity.Generation.SubjectABI
public meta import ZkcSecurity.Generation.SubjectABI
public import ZkcSecurity.Generation.OriginalEndpoint
public import ZkcSecurity.Generation.OriginalSecurityBindingsCatalogue
public meta import ZkcSecurity.Generation.OriginalSecurityBindingsCatalogue
public meta import ZkcSecurity.Generation.OriginalEndpoint
public import ZkcSecurity.Generation.RootCompleteness
public meta import ZkcSecurity.Generation.RootCompleteness

public import ZkcSecurity.Generation.OriginalRootCatalogue
public meta import ZkcSecurity.Generation.OriginalRootCatalogue
public import ZkcSecurity.Generation.ConstructionBindingsCatalogue
public meta import ZkcSecurity.Generation.ConstructionBindingsCatalogue
public import ZkcSecurity.Generation.TargetSourceAliasesCatalogue
public meta import ZkcSecurity.Generation.TargetSourceAliasesCatalogue

@[expose] public section

/-! Production endpoints consume installed original-source laws. The catalogue
owns proof selection; admitted ABIs and artifacts supply structural metadata.
Old compiled matcher outputs are generated only by regression drivers. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace ZkcSecurity.Generation.Roots
open ZkcTools.StructuredSource.Root
open ZkcSecurity.Generation

def soundnessOutput (root : Selection) : OriginalEndpoint.Output where
  moduleName := root.componentModule "Soundness"
  subjectModule := root.subjectModule
  methodModule := root.securityModule ++ ".Soundness"
  sampling := root.mathematics.modelModule ++ "." ++ root.mathematics.sampling
  capabilities := root.mathematics.modelModule ++ "." ++ root.mathematics.capabilities
  schedule := root.securityModule ++ ".Soundness.schedule"
  validatorCost := root.securityModule ++ ".Soundness.validatorCost"
  chargedExport := root.securityModule ++ ".Soundness.reductionExport"
  scalar := some ⟨root.securityModule ++ ".Soundness.scalarBound", root.securityModule ++ ".Soundness.scalar_bound"⟩

def completenessSelection (root : Selection) : RootCompleteness.Selection where
  moduleName := root.componentModule "Completeness"
  subjectModule := root.subjectModule
  error := .zero

def completenessClaimsOutput (root : Selection) : FixedCompletenessOutput :=
  RootCompleteness.claimsOutput (completenessSelection root) {
    capabilities := root.mathematics.modelModule ++ "." ++ root.mathematics.capabilities }

def claimLibraryOutput (root : Selection) : DomainClaimLibraryOutput :=
  let proofs := root.componentModule "Soundness"
  { moduleName := root.subjectModule ++ "SoundnessRegistration"
    imports := [root.subjectModule, proofs]
    subjectExpression := root.subjectModule ++ ".validatorSubject"
    artifactsExpression := root.subjectModule ++ ".validatorArtifacts"
    capabilitiesExpression := proofs ++ ".capabilities"
    applicationParameter := some "application"
    theoremMethods := [("fs.keyed_soundness", 0, proofs ++ ".scalar_meaning"),
      ("fs.keyed_charged", 0, proofs ++ ".charged_meaning")]
    theoremNormalization := [proofs ++ ".schedule", proofs ++ ".validatorCost", proofs ++ ".scalarBound"] ++
      ["schedule", "price", "priceBound", "budget", "validatorCost", "scalarBound"].map
        (fun name => root.securityModule ++ ".Soundness." ++ name) ++
      ["ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"] }

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let mut sources : List (String × String × String) :=
    (OriginalRootCatalogue.sources ++ ConstructionBindingsCatalogue.sources ++
      TargetSourceAliasesCatalogue.sources).map fun (name, source) => ("bindings", name, source)
  for root in ← evaluateSelections do
    let metadata ← Lean.Elab.Command.liftTermElabM do
      let subject := Lean.mkIdent ((root.subjectModule ++ ".subject").toName)
      let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata $subject)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
    let pair := root.artifacts
    sources := sources ++ [
      ("abi", root.componentModule "ABI", ← require <| SubjectABI.source metadata {
        moduleName := root.componentModule "ABI", subjectModule := root.subjectModule }),
      ("soundness", root.componentModule "Soundness", ← require <| OriginalEndpoint.soundnessSource metadata pair.validator (soundnessOutput root)),
      ("completeness", root.componentModule "Completeness", RootCompleteness.directSource
        (completenessSelection root) (root.securityModule ++ ".Completeness")
        (root.securityModule ++ ".Completeness.compiled_ideal_complete") root.mathematics.sampling
        ["ZkcSecurity.Domains.PrimeField"]),
      ("completeness-claims", root.subjectModule ++ "CompletenessClaims", fixedCompletenessSource (completenessClaimsOutput root)),
      ("claim-libraries", root.subjectModule ++ "SoundnessRegistration", domainClaimLibrarySource (claimLibraryOutput root))]
    for (name, source) in OriginalSecurityBindingsCatalogue.sources do
      if name.startsWith (root.securityModule ++ ".") then
        let stage := if name.endsWith ".Sources" || name.endsWith ".Installation" || name.endsWith ".Soundness"
          then "soundness" else "completeness"
        sources := sources ++ [(stage, name, source)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `stageSources) : List (String × String × String) := $(Lean.quote sources)))

def generateStage (stage : String) (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  unless stageSources.any (fun (selected, _, _) => selected == stage) do
    throw (IO.userError ("unknown production generation stage: " ++ stage))
  writeSources directory (stageSources.filterMap fun (selected, name, source) =>
    if selected == stage then some (name, source) else none)

end ZkcSecurity.Generation.Roots
