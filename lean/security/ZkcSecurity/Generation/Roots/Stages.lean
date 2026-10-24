module

public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.SubjectImports
public import ZkcSecurity.Generation.SubjectABI
public meta import ZkcSecurity.Generation.SubjectABI
public import ZkcSecurity.Generation.SumcheckCompleteness
public meta import ZkcSecurity.Generation.SumcheckCompleteness
public import ZkcSecurity.Generation.SumcheckSoundness
public meta import ZkcSecurity.Generation.SumcheckSoundness

@[expose] public section

/-! The installed Sumcheck family generates each production stage from the
same selections. Its existing pattern matcher remains the applicability check;
this assembly does not establish original-component correspondence. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace ZkcSecurity.Generation.Roots
open ZkcTools.StructuredSource.Root
open ZkcSecurity.Generation

/-- All physical module names follow the catalogue's one naming convention. -/
def roundOutput (root : Selection) : RoundDescriptors.Output where
  moduleName := root.componentModule "Rounds"
  producerModule := root.constructedModule "Producer"
  validatorModule := root.constructedModule "Validator"
  contextModule := root.subjectModule
  contextExpression := root.subjectModule ++ ".subject.selection.context"

def viewOutput (root : Selection) : SumcheckViews.Output where
  moduleName := root.componentModule "ValidatorView"
  subjectModule := root.subjectModule
  validatorModule := root.constructedModule "Validator"
  roundsModule := root.componentModule "Rounds"

def soundnessOutput (root : Selection) : SumcheckSoundness.Output where
  moduleName := root.componentModule "Soundness"
  subjectModule := root.subjectModule
  roundsModule := root.componentModule "Rounds"
  validatorViewModule := root.componentModule "ValidatorView"
  abiModule := root.componentModule "ABI"
  mathematicsModule := root.formulaNamespace.replace ".Formula" "Formula"
  formulaLaw := root.formulaNamespace ++ ".equation"
  modulus := root.mathematics.modulus
  capabilities := root.mathematics.capabilities
  fieldType := root.mathematics.fieldType
  groupType := root.mathematics.groupType
  sampling := root.mathematics.sampling

def completenessOutput (root : Selection) : SumcheckCompleteness.Output where
  moduleName := root.componentModule "Completeness"
  subjectModule := root.subjectModule
  producerModule := root.constructedModule "Producer"
  validatorModule := root.constructedModule "Validator"
  roundsModule := root.componentModule "Rounds"
  validatorViewModule := root.componentModule "ValidatorView"
  abiModule := root.componentModule "ABI"
  mathematicsModule := root.formulaNamespace.replace ".Formula" "Formula"
  formulaLaw := root.formulaNamespace ++ ".equation"
  nonvacuityLaw := root.formulaNamespace ++ ".nonvacuous"
  fieldType := root.mathematics.fieldType
  groupType := root.mathematics.groupType
  sampling := root.mathematics.sampling

def completenessClaimsOutput (root : Selection) : FixedCompletenessOutput where
  moduleName := root.subjectModule ++ "CompletenessClaims"
  subjectModule := root.subjectModule
  subjectNamespace := root.subjectModule
  proofModule := root.componentModule "Completeness"
  proofName := root.componentModule "Completeness" ++ ".compiled_ideal_complete"
  capabilitiesExpression := root.mathematics.modelModule ++ "." ++ root.mathematics.capabilities

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
    theoremNormalization := [proofs ++ ".price", proofs ++ ".priceBound", proofs ++ ".budget", proofs ++ ".schedule",
      "ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"] }

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let mut sources : List (String × String × String) := []
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
      ("rounds", root.componentModule "Rounds", ← require <| RoundDescriptors.source pair.producer pair.validator (roundOutput root)),
      ("views", root.componentModule "ValidatorView", ← require <| SumcheckViews.source pair.producer pair.validator (viewOutput root)),
      ("soundness", root.componentModule "Soundness", ← require <| SumcheckSoundness.source {
        metadata, producer := pair.producer, validator := pair.validator, output := soundnessOutput root }),
      ("completeness", root.componentModule "Completeness", ← require <| SumcheckCompleteness.source {
        metadata, producer := pair.producer, validator := pair.validator, output := completenessOutput root }),
      ("completeness-claims", root.subjectModule ++ "CompletenessClaims", fixedCompletenessSource (completenessClaimsOutput root)),
      ("claim-libraries", root.subjectModule ++ "SoundnessRegistration", domainClaimLibrarySource (claimLibraryOutput root))]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `stageSources) : List (String × String × String) := $(Lean.quote sources)))

def generateStage (stage : String) (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  writeSources directory (stageSources.filterMap fun (selected, name, source) =>
    if selected == stage then some (name, source) else none)

end ZkcSecurity.Generation.Roots
