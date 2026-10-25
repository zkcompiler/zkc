module

public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue
public import ZkcSecurity.Generation.OriginalSecurityBindingsHonest
public meta import ZkcSecurity.Generation.OriginalSecurityBindingsHonest
public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcSecurity.Examples.Generated.TwoSums
public meta import ZkcSecurity.Examples.Generated.SmallSumcheck
public meta import ZkcSecurity.Examples.Generated.TwoSums

@[expose] public section
namespace ZkcSecurity.Generation.OriginalSecurityBindingsCatalogue

run_cmd do
  let mut sources : List (String × String) := []
  for root in ← Roots.evaluateSelections do
    let program ← match Zkc.Source.Structured.check root.snapshot with
      | .ok value => pure value
      | .error reason => throwError "{root.name}: {reason}"
    let binding ← match OriginalSecurityBindings.analyze program root.artifacts.validator root.artifacts.producer with
      | .ok value => pure value
      | .error reason => throwError "{root.name}: {reason}"
    let metadata ← Lean.Elab.Command.liftTermElabM do
      let subject := Lean.mkIdent ((root.subjectModule ++ ".subject").toName)
      let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata $subject)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
    match OriginalSecurityBindings.validateABI program binding metadata with
    | .ok () => pure ()
    | .error reason => throwError "{root.name}: {reason}"
    let moduleName := "ZkcSecurity.Examples.Generated.OriginalSecurity." ++ root.name
    let output : OriginalSecurityBindings.Output := {
      moduleName, originalModule := "ZkcExamples.Structured.Generated.Original." ++ root.name
      artifactModule := "ZkcSecurity.Examples.Generated.OriginalArtifacts." ++ root.name
      subjectModule := root.subjectModule, abiModule := root.componentModule "ABI"
      formulaNamespace := root.formulaNamespace, fieldType := root.mathematics.fieldType
      groupType := root.mathematics.groupType, modulus := root.mathematics.modulus
      sampling := root.mathematics.sampling, capabilities := root.mathematics.capabilities }
    let generated ← match OriginalSecurityBindings.sourceBindings program binding output with
      | .ok value => pure value
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(moduleName ++ ".Sources", generated)]
    for (suffix, candidate) in [(".Installation", OriginalSecurityBindings.installationBindings program binding output),
        (".Soundness", OriginalSecurityBindings.soundnessBindings program binding output),
        (".Honest", OriginalSecurityBindings.honestBindings program binding output),
        (".Completeness", OriginalSecurityBindings.completenessBindings program binding output)] do
      let generated ← match candidate with
        | .ok value => pure value
        | .error reason => throwError "{root.name}: {reason}"
      sources := sources ++ [(moduleName ++ suffix, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

end ZkcSecurity.Generation.OriginalSecurityBindingsCatalogue
